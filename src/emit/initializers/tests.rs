use crate::{Options, Source, decompile};

const OWNER: &str = "example/Fixture";

struct Fixture {
    pool: Vec<Vec<u8>>,
    fields: Vec<[u16; 4]>,
    methods: Vec<Vec<u8>>,
    this: u16,
    object: u16,
}

impl Fixture {
    fn new() -> Self {
        let mut fixture = Self {
            pool: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            this: 0,
            object: 0,
        };
        fixture.this = fixture.class(OWNER);
        fixture.object = fixture.class("java/lang/Object");
        fixture
    }

    fn constant(&mut self, tag: u8, bytes: &[u8]) -> u16 {
        let mut entry = vec![tag];
        entry.extend_from_slice(bytes);
        self.pool.push(entry);
        self.pool.len() as u16
    }

    fn utf8(&mut self, text: &str) -> u16 {
        let mut bytes = (text.len() as u16).to_be_bytes().to_vec();
        bytes.extend_from_slice(text.as_bytes());
        self.constant(1, &bytes)
    }

    fn class(&mut self, name: &str) -> u16 {
        let name = self.utf8(name);
        self.constant(7, &name.to_be_bytes())
    }

    fn field(&mut self, flags: u16, name: &str, descriptor: &str) -> u16 {
        let field_name = self.utf8(name);
        let field_type = self.utf8(descriptor);
        self.fields.push([flags, field_name, field_type, 0]);
        // Separate Utf8 entries in the declaration and reference are valid.
        self.member_ref(9, self.this, name, descriptor)
    }

    fn member_ref(&mut self, tag: u8, owner: u16, name: &str, descriptor: &str) -> u16 {
        let name = self.utf8(name);
        let descriptor = self.utf8(descriptor);
        let name_type = self.constant(12, &words([name, descriptor]));
        self.constant(tag, &words([owner, name_type]))
    }

    fn method(
        &mut self,
        flags: u16,
        name: &str,
        descriptor: &str,
        code: &[u8],
        lines: &[(u16, u16)],
    ) {
        let name = self.utf8(name);
        let descriptor = self.utf8(descriptor);
        let code_name = self.utf8("Code");
        let mut body = words([8, 4]);
        body.extend((code.len() as u32).to_be_bytes());
        body.extend_from_slice(code);
        body.extend(words([0, u16::from(!lines.is_empty())]));
        if !lines.is_empty() {
            let line_name = self.utf8("LineNumberTable");
            body.extend(line_name.to_be_bytes());
            body.extend((2 + 4 * lines.len() as u32).to_be_bytes());
            body.extend((lines.len() as u16).to_be_bytes());
            body.extend(words(
                lines.iter().flat_map(|&(offset, line)| [offset, line]),
            ));
        }
        let mut method = words([flags, name, descriptor, 1, code_name]);
        method.extend((body.len() as u32).to_be_bytes());
        method.extend(body);
        self.methods.push(method);
    }

    fn source(self) -> Source {
        self.source_with(|_| {})
    }

    fn source_with(self, configure: impl FnOnce(&mut Options)) -> Source {
        let mut bytes = 0xcafe_babeu32.to_be_bytes().to_vec();
        bytes.extend(words([0, 52, self.pool.len() as u16 + 1]));
        bytes.extend(self.pool.into_iter().flatten());
        bytes.extend(words([
            0x0021,
            self.this,
            self.object,
            0,
            self.fields.len() as u16,
        ]));
        bytes.extend(words(self.fields.into_iter().flatten()));
        bytes.extend((self.methods.len() as u16).to_be_bytes());
        bytes.extend(self.methods.into_iter().flatten());
        bytes.extend(0u16.to_be_bytes());
        let mut options = Options::default();
        options.include_line_mappings = true;
        configure(&mut options);
        decompile(&bytes, &options).unwrap()
    }
}

fn words(values: impl IntoIterator<Item = u16>) -> Vec<u8> {
    values.into_iter().flat_map(u16::to_be_bytes).collect()
}

fn reference(opcode: u8, index: u16) -> [u8; 3] {
    let [hi, lo] = index.to_be_bytes();
    [opcode, hi, lo]
}

fn line_of(source: &Source, text: &str) -> usize {
    source
        .text
        .lines()
        .position(|line| line.contains(text))
        .unwrap_or_else(|| panic!("missing {text:?} in {}", source.text))
}

#[test]
fn descending_static_targets_keep_the_bytecode_order() {
    let mut f = Fixture::new();
    let sizes = f.field(0x000a, "sizes", "[I");
    let names = f.field(0x000a, "names", "[I");
    let size = f.field(0x001a, "SIZE", "I");
    let code = [
        &[0x05, 0xbc, 10][..],
        &reference(0xb3, names),
        &reference(0xb2, names),
        &[0xbe, 0xbc, 10],
        &reference(0xb3, sizes),
        &reference(0xb2, sizes),
        &[0xbe],
        &reference(0xb3, size),
        &[0xb1],
    ]
    .concat();
    f.method(
        0x0008,
        "<clinit>",
        "()V",
        &code,
        &[(0, 9), (6, 14), (15, 16), (22, 17)],
    );
    let source = f.source();
    let names = line_of(&source, "int[] names = new int[2];");
    let block = line_of(&source, "static {");
    let sizes = line_of(&source, "Fixture.sizes = new int[Fixture.names.length];");
    let size = line_of(&source, "SIZE = Fixture.sizes.length;");
    assert!(
        line_of(&source, "int[] sizes;") < names && names < block && block < sizes && sizes < size
    );
    let map = source.map.unwrap();
    assert_eq!(map.methods.len(), 1);
    assert_eq!(map.methods[0].name, "<clinit>");
    assert_eq!(map.methods[0].offsets[&0], names);
    assert_eq!(map.methods[0].offsets[&5], names);
    assert_eq!(map.methods[0].offsets[&6], sizes);
    assert_eq!(map.original_lines[&9], names + 1);
    assert_eq!(map.original_lines[&14], sizes + 1);
    assert_eq!(map.original_lines[&16], size + 1);
}

#[test]
fn ascending_dependencies_move_but_an_explicit_statement_is_a_barrier() {
    let mut f = Fixture::new();
    let first = f.field(0x0008, "first", "I");
    let second = f.field(0x0018, "second", "I");
    let last = f.field(0x0008, "last", "I");
    let callback = f.member_ref(10, f.this, "callback", "()V");
    f.method(0x0008, "callback", "()V", &[0xb1], &[]);
    let code = [
        &[0x04][..],
        &reference(0xb3, first),
        &reference(0xb2, first),
        &[0x04, 0x60],
        &reference(0xb3, second),
        &reference(0xb8, callback),
        &[0x06],
        &reference(0xb3, last),
        &[0xb1],
    ]
    .concat();
    f.method(0x0008, "<clinit>", "()V", &code, &[]);
    let source = f.source();
    let first = line_of(&source, "int first = 1;");
    let second = line_of(&source, "final int second = Fixture.first + 1;");
    let callback = line_of(&source, "callback();");
    let last = line_of(&source, "Fixture.last = 3;");
    assert!(first < second && second < callback && callback < last);
}

#[test]
fn blank_final_literals_keep_runtime_assignment_and_linkage() {
    let mut f = Fixture::new();
    let field = f.field(0x0018, "RUNTIME", "I");
    let code = [&[0x07][..], &reference(0xb3, field), &[0xb1]].concat();
    f.method(0x0008, "<clinit>", "()V", &code, &[]);
    let source = f.source();
    assert!(line_of(&source, "static final int RUNTIME;") < line_of(&source, "RUNTIME = 4;"));
}

#[test]
fn a_hidden_static_field_is_a_barrier_for_later_declarations() {
    let mut f = Fixture::new();
    let hidden = f.field(0x1008, "compilerState", "I");
    let visible = f.field(0x0008, "state", "I");
    let code = [
        &[0x04][..],
        &reference(0xb3, hidden),
        &[0x05],
        &reference(0xb3, visible),
        &[0xb1],
    ]
    .concat();
    f.method(0x0008, "<clinit>", "()V", &code, &[]);
    let source = f.source();
    let declaration = line_of(&source, "static int state;");
    let hidden_write = line_of(&source, "Fixture.compilerState = 1;");
    let visible_write = line_of(&source, "Fixture.state = 2;");
    assert!(declaration < hidden_write && hidden_write < visible_write);
}

#[test]
fn common_post_super_assignments_move_once_and_keep_both_constructor_maps() {
    let mut f = Fixture::new();
    let common = f.field(0, "common", "I");
    let other = f.field(0, "other", "I");
    let super_call = reference(0xb7, f.member_ref(10, f.object, "<init>", "()V"));
    let delegate = reference(0xb7, f.member_ref(10, f.this, "<init>", "(I)V"));
    let empty = [
        &[0x2a][..],
        &super_call,
        &[0x2a, 0x04],
        &reference(0xb5, common),
        &[0x2a, 0x05],
        &reference(0xb5, other),
        &[0xb1],
    ]
    .concat();
    let one_arg = [
        &[0x2a][..],
        &super_call,
        &[0x2a, 0x04],
        &reference(0xb5, common),
        &[0x2a, 0x1b],
        &reference(0xb5, other),
        &[0xb1],
    ]
    .concat();
    let delegated = [
        &[0x2a, 0x1b][..],
        &delegate,
        &[0x2a, 0x06],
        &reference(0xb5, common),
        &[0xb1],
    ]
    .concat();
    f.method(1, "<init>", "()V", &empty, &[(0, 10), (4, 11), (9, 12)]);
    f.method(1, "<init>", "(I)V", &one_arg, &[(0, 20), (4, 21), (9, 22)]);
    f.method(1, "<init>", "(II)V", &delegated, &[(0, 30), (5, 31)]);
    let source = f.source();
    let declaration = line_of(&source, "int common = 1;");
    assert_eq!(source.text.matches("common = 1;").count(), 1);
    assert!(source.text.contains("this.other = 2;"));
    assert!(source.text.contains("this.common = 3;"));
    assert!(!source.text.contains("int other ="));
    let map = source.map.unwrap();
    for descriptor in ["()V", "(I)V"] {
        let mut method = map
            .methods
            .iter()
            .filter(|method| method.name == "<init>" && method.descriptor == descriptor);
        assert_eq!(method.next().unwrap().offsets[&4], declaration);
        assert!(method.next().is_none());
    }
    assert_eq!(map.original_lines[&11], declaration + 1);
    assert_eq!(map.original_lines[&21], declaration + 1);
    assert_ne!(map.original_lines[&31], declaration + 1);
}

#[test]
fn a_post_super_putfield_on_another_receiver_never_initializes_this() {
    let mut f = Fixture::new();
    let peer = f.field(0x0008, "peer", "Lexample/Fixture;");
    let field = f.field(0, "value", "I");
    let super_call = reference(0xb7, f.member_ref(10, f.object, "<init>", "()V"));
    let code = [
        &[0x2a][..],
        &super_call,
        &reference(0xb2, peer),
        &[0x06],
        &reference(0xb5, field),
        &[0xb1],
    ]
    .concat();
    f.method(1, "<init>", "()V", &code, &[]);
    let source = f.source();
    assert!(line_of(&source, "int value;") < line_of(&source, "Fixture.peer.value = 3;"));
}

#[test]
fn divergent_instance_prefixes_stay_in_their_own_constructors() {
    let mut f = Fixture::new();
    let field = f.field(0, "value", "I");
    let super_call = reference(0xb7, f.member_ref(10, f.object, "<init>", "()V"));
    for (descriptor, value) in [("()V", 0x04), ("(I)V", 0x05)] {
        let code = [
            &[0x2a][..],
            &super_call,
            &[0x2a, value],
            &reference(0xb5, field),
            &[0xb1],
        ]
        .concat();
        f.method(1, "<init>", descriptor, &code, &[]);
    }
    let source = f.source();
    assert!(source.text.contains("int value;"));
    assert!(source.text.contains("this.value = 1;"));
    assert!(source.text.contains("this.value = 2;"));
}

#[test]
fn a_branch_keeps_the_guarded_store_in_clinit() {
    let mut f = Fixture::new();
    let condition = f.field(0x0008, "condition", "Z");
    let first = f.field(0x0008, "first", "I");
    let second = f.field(0x0008, "second", "I");
    let code = [
        &[0x04][..],
        &reference(0xb3, first),
        &reference(0xb2, condition),
        &[0x99, 0, 7, 0x05],
        &reference(0xb3, second),
        &[0xb1],
    ]
    .concat();
    f.method(0x0008, "<clinit>", "()V", &code, &[]);
    let source = f.source();
    let initializer = line_of(&source, "int first = 1;");
    let branch = line_of(&source, "if (");
    let store = line_of(&source, "Fixture.second = 2;");
    assert!(initializer < branch && branch < store);
}

#[test]
fn renamed_initializer_reads_still_resolve_to_the_declared_field() {
    let mut f = Fixture::new();
    let first = f.field(0x0008, "a", "I");
    let second = f.field(0x0008, "second", "I");
    let code = [
        &[0x04][..],
        &reference(0xb3, first),
        &reference(0xb2, first),
        &reference(0xb3, second),
        &[0xb1],
    ]
    .concat();
    f.method(0x0008, "<clinit>", "()V", &code, &[]);
    let source = f.source_with(|options| options.rename_members = true);
    assert!(source.text.contains("int field_0 = 1;"));
    assert!(source.text.contains("int second = Fixture.field_0;"));
}

#[test]
fn an_elided_default_constructor_still_maps_its_initializer() {
    let mut f = Fixture::new();
    let field = f.field(0, "value", "I");
    let super_call = reference(0xb7, f.member_ref(10, f.object, "<init>", "()V"));
    let code = [
        &[0x2a][..],
        &super_call,
        &[0x2a, 0x04],
        &reference(0xb5, field),
        &[0xb1],
    ]
    .concat();
    f.method(1, "<init>", "()V", &code, &[(0, 10), (4, 11)]);
    let source = f.source();
    let declaration = line_of(&source, "int value = 1;");
    assert!(!source.text.contains("Fixture()"));
    let map = source.map.unwrap();
    assert_eq!(map.methods[0].name, "<init>");
    assert_eq!(map.methods[0].offsets[&4], declaration);
    assert_eq!(map.original_lines[&11], declaration + 1);
}

fn array_field_fixture() -> Fixture {
    let mut f = Fixture::new();
    let field = f.field(0x0018, "numbers", "[I");
    let code = [
        &[
            0x05, 0xbc, 10, 0x59, 0x03, 0x04, 0x4f, 0x59, 0x04, 0x05, 0x4f,
        ][..],
        &reference(0xb3, field),
        &[0xb1],
    ]
    .concat();
    f.method(0x0008, "<clinit>", "()V", &code, &[(0, 9)]);
    f
}

#[test]
fn literal_arrays_at_the_start_of_clinit_are_declaration_initializers() {
    let source = array_field_fixture().source();
    let declaration = line_of(&source, "static final int[] numbers = new int[]{1, 2};");
    assert!(!source.text.contains("static {"));
    assert_eq!(source.map.unwrap().methods[0].offsets[&10], declaration);
}

#[test]
fn recovered_field_initializer_retains_its_document_breaks() {
    let source = array_field_fixture().source_with(|options| options.preferred_line_length = 28);
    let declaration = line_of(&source, "static final int[] numbers = new int[]{");
    let elements = line_of(&source, "1, 2");
    let closing = line_of(&source, "};");
    assert_eq!(elements, declaration + 1);
    assert_eq!(closing, elements + 1);
    assert_eq!(source.map.unwrap().methods[0].offsets[&10], declaration);
}

#[test]
fn array_elements_cannot_hide_a_constructor_parameter_from_declaration_proof() {
    let mut f = Fixture::new();
    let field = f.field(0, "numbers", "[I");
    let super_call = reference(0xb7, f.member_ref(10, f.object, "<init>", "()V"));
    let code = [
        &[0x2a][..],
        &super_call,
        &[0x2a, 0x04, 0xbc, 10, 0x59, 0x03, 0x1b, 0x4f],
        &reference(0xb5, field),
        &[0xb1],
    ]
    .concat();
    f.method(1, "<init>", "(I)V", &code, &[]);
    let source = f.source();
    assert!(source.text.contains("int[] numbers;"));
    assert!(source.text.contains("this.numbers = new int[]{"));
}
