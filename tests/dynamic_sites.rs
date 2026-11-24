// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use vineflower_rs::{ClassGroupBuilder, Options, decompile};

const SAMPLE: &str = "example/DynamicSites";
const META: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;";
const ALT: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;";
const CONDY: &str = "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/Class;";

#[derive(Default)]
struct Class {
    pool: Vec<Vec<u8>>,
    methods: Vec<Vec<u8>>,
    bootstraps: Vec<Vec<u8>>,
}

impl Class {
    fn entry(&mut self, tag: u8, bytes: &[u8]) -> u16 {
        let mut entry = vec![tag];
        entry.extend_from_slice(bytes);
        self.pool.push(entry);
        u16::try_from(self.pool.len()).unwrap()
    }

    fn utf8(&mut self, text: &str) -> u16 {
        let mut payload = words(&[u16::try_from(text.len()).unwrap()]);
        payload.extend_from_slice(text.as_bytes());
        self.entry(1, &payload)
    }

    fn class(&mut self, text: &str) -> u16 {
        let name = self.utf8(text);
        self.entry(7, &name.to_be_bytes())
    }

    fn name_type(&mut self, name: &str, descriptor: &str) -> u16 {
        let name = self.utf8(name);
        let descriptor = self.utf8(descriptor);
        self.entry(12, &words(&[name, descriptor]))
    }

    fn method_ref(&mut self, owner: &str, name: &str, descriptor: &str) -> u16 {
        let owner = self.class(owner);
        let name_type = self.name_type(name, descriptor);
        self.entry(10, &words(&[owner, name_type]))
    }

    fn method_type(&mut self, descriptor: &str) -> u16 {
        let descriptor = self.utf8(descriptor);
        self.entry(16, &descriptor.to_be_bytes())
    }

    fn handle(&mut self, kind: u8, owner: &str, name: &str, descriptor: &str) -> u16 {
        let [high, low] = self.method_ref(owner, name, descriptor).to_be_bytes();
        self.entry(15, &[kind, high, low])
    }

    fn dynamic(&mut self, tag: u8, handle: u16, args: &[u16], name: &str, ty: &str) -> u16 {
        let index = self.bootstraps.len() as u16;
        let mut bootstrap = words(&[handle, args.len() as u16]);
        bootstrap.extend(words(args));
        self.bootstraps.push(bootstrap);
        let name_type = self.name_type(name, ty);
        self.entry(tag, &words(&[index, name_type]))
    }

    fn lambda(
        &mut self,
        target: u16,
        name: &str,
        factory: &str,
        erased: &str,
        instantiated: &str,
        alternate: Option<&[u16]>,
    ) -> [u8; 5] {
        let (bootstrap_name, bootstrap_descriptor) = if alternate.is_some() {
            ("altMetafactory", ALT)
        } else {
            ("metafactory", META)
        };
        let handle = self.handle(
            6,
            "java/lang/invoke/LambdaMetafactory",
            bootstrap_name,
            bootstrap_descriptor,
        );
        let mut args = vec![
            self.method_type(erased),
            target,
            self.method_type(instantiated),
        ];
        args.extend_from_slice(alternate.unwrap_or_default());
        let [high, low] = self.dynamic(18, handle, &args, name, factory).to_be_bytes();
        [0xba, high, low, 0, 0]
    }

    fn constant(
        &mut self,
        bootstrap: &str,
        suffix: &str,
        args: &[u16],
        name: &str,
        ty: &str,
    ) -> [u8; 3] {
        let handle = self.handle(
            6,
            "java/lang/invoke/ConstantBootstraps",
            bootstrap,
            &format!("{CONDY}{suffix}"),
        );
        let [high, low] = self.dynamic(17, handle, args, name, ty).to_be_bytes();
        [0x13, high, low]
    }

    fn method(&mut self, flags: u16, name: &str, descriptor: &str, instructions: &[u8]) {
        let name = self.utf8(name);
        let descriptor = self.utf8(descriptor);
        let code = self.utf8("Code");
        let mut body = words(&[8, 8]);
        body.extend((instructions.len() as u32).to_be_bytes());
        body.extend_from_slice(instructions);
        body.extend(words(&[0, 0]));
        let mut method = words(&[flags, name, descriptor, 1]);
        method.extend(attribute(code, &body));
        self.methods.push(method);
    }

    fn finish(self) -> Vec<u8> {
        self.finish_as(SAMPLE, 0x0021, &[], None)
    }

    fn finish_as(
        mut self,
        name: &str,
        flags: u16,
        interfaces: &[&str],
        signature: Option<&str>,
    ) -> Vec<u8> {
        let this = self.class(name);
        let object = self.class("java/lang/Object");
        let bootstrap_methods = self.utf8("BootstrapMethods");
        let interfaces: Vec<_> = interfaces.iter().map(|name| self.class(name)).collect();
        let signature = signature.map(|text| (self.utf8("Signature"), self.utf8(text)));
        let mut bytes = 0xcafe_babeu32.to_be_bytes().to_vec();
        bytes.extend(words(&[0, 65, self.pool.len() as u16 + 1]));
        bytes.extend(self.pool.into_iter().flatten());
        bytes.extend(words(&[flags, this, object, interfaces.len() as u16]));
        bytes.extend(words(&interfaces));
        bytes.extend(words(&[0, self.methods.len() as u16]));
        bytes.extend(self.methods.into_iter().flatten());
        bytes.extend(words(&[1 + u16::from(signature.is_some())]));
        let mut bootstraps = words(&[self.bootstraps.len() as u16]);
        bootstraps.extend(self.bootstraps.into_iter().flatten());
        bytes.extend(attribute(bootstrap_methods, &bootstraps));
        if let Some((tag, value)) = signature {
            bytes.extend(attribute(tag, &value.to_be_bytes()));
        }
        bytes
    }

    fn source(self) -> String {
        decompile(&self.finish(), &Options::default()).unwrap().text
    }
}

fn words(words: &[u16]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_be_bytes()).collect()
}

fn attribute(name: u16, payload: &[u8]) -> Vec<u8> {
    let mut bytes = name.to_be_bytes().to_vec();
    bytes.extend((payload.len() as u32).to_be_bytes());
    bytes.extend_from_slice(payload);
    bytes
}

#[test]
fn emits_typed_unbound_bound_and_constructor_references() {
    let mut class = Class::default();
    let length = class.handle(5, "java/lang/String", "length", "()I");
    let function = "()Ljava/util/function/Function;";
    let indy = class.lambda(
        length,
        "apply",
        function,
        "(Ljava/lang/Object;)Ljava/lang/Object;",
        "(Ljava/lang/String;)Ljava/lang/Integer;",
        None,
    );
    class.method(9, "unbound", function, &[indy.as_slice(), &[0xb0]].concat());

    class.method(9, "receiver", "()Ljava/lang/String;", &[0x01, 0xb0]);
    let receiver = class.method_ref(SAMPLE, "receiver", "()Ljava/lang/String;");
    let [high, low] = receiver.to_be_bytes();
    let indy = class.lambda(
        length,
        "getAsInt",
        "(Ljava/lang/String;)Ljava/util/function/IntSupplier;",
        "()I",
        "()I",
        None,
    );
    class.method(
        9,
        "bound",
        "()Ljava/util/function/IntSupplier;",
        &[&[0xb8, high, low], indy.as_slice(), &[0xb0]].concat(),
    );

    let init = class.handle(8, "java/lang/StringBuilder", "<init>", "()V");
    let supplier = "()Ljava/util/function/Supplier;";
    let indy = class.lambda(
        init,
        "get",
        supplier,
        "()Ljava/lang/Object;",
        "()Ljava/lang/StringBuilder;",
        None,
    );
    class.method(
        9,
        "constructor",
        supplier,
        &[indy.as_slice(), &[0xb0]].concat(),
    );

    let text = class.source();
    assert!(
        text.contains("Function<String, Integer>)String::length"),
        "{text}"
    );
    assert!(text.contains("receiver()::length"), "{text}");
    assert_eq!(text.matches("receiver()").count(), 2, "{text}"); // declaration and one call
    assert!(
        text.contains("Supplier<StringBuilder>)StringBuilder::new"),
        "{text}"
    );
}

#[test]
fn substitutes_type_parameters_in_an_inherited_generic_sam() {
    let mut class = Class::default();
    let target = class.handle(5, "java/lang/String", "length", "()I");
    let factory = "()Lexample/Mapping;";
    let indy = class.lambda(
        target,
        "apply",
        factory,
        "(Ljava/lang/Object;)Ljava/lang/Object;",
        "(Ljava/lang/String;)Ljava/lang/Integer;",
        None,
    );
    class.method(9, "mapping", factory, &[indy.as_slice(), &[0xb0]].concat());
    let bytes = class.finish();
    let interface = Class::default().finish_as(
        "example/Mapping",
        0x0601,
        &["java/util/function/Function"],
        Some("<T:Ljava/lang/Object;>Ljava/lang/Object;Ljava/util/function/Function<TT;Ljava/lang/Integer;>;"),
    );
    let mut group = ClassGroupBuilder::default();
    group.add(&bytes).unwrap();
    group.add_library(&interface).unwrap();
    let group = group.build().unwrap();
    let text = group.decompile(SAMPLE, &Options::default()).unwrap().text;
    assert!(text.contains("Mapping<String>)String::length"), "{text}");
}

#[test]
fn names_the_linked_overload_in_a_widening_adapter() {
    let mut class = Class::default();
    class.method(9, "widen", "(J)J", &[0x1e, 0xad]);
    class.method(9, "widen", "(I)J", &[0x09, 0xad]);
    let method = class.handle(6, SAMPLE, "widen", "(J)J");
    let factory = "()Ljava/util/function/IntToLongFunction;";
    let indy = class.lambda(method, "applyAsLong", factory, "(I)J", "(I)J", None);
    class.method(9, "factory", factory, &[indy.as_slice(), &[0xb0]].concat());
    let text = class.source();
    assert!(text.contains("-> DynamicSites.widen((long)("), "{text}");
    assert!(!text.contains("::widen"), "{text}");
}

#[test]
fn inlines_generated_bodies_and_preserves_serializable_markers() {
    let mut class = Class::default();
    let helper = class.handle(6, SAMPLE, "lambda$factory$0", "()V");
    let flags = class.entry(3, &7i32.to_be_bytes());
    let one = class.entry(3, &1i32.to_be_bytes());
    let zero = class.entry(3, &0i32.to_be_bytes());
    let marker = class.class("java/lang/Cloneable");
    let factory = "()Ljava/lang/Runnable;";
    let indy = class.lambda(
        helper,
        "run",
        factory,
        "()V",
        "()V",
        Some(&[flags, one, marker, zero]),
    );
    class.method(9, "factory", factory, &[indy.as_slice(), &[0xb0]].concat());
    class.method(0x100a, "lambda$factory$0", "()V", &[0xb1]);

    let capture = "(I)Ljava/util/function/IntUnaryOperator;";
    let helper = class.handle(6, SAMPLE, "lambda$capture$1", "(II)I");
    let indy = class.lambda(helper, "applyAsInt", capture, "(I)I", "(I)I", None);
    class.method(
        9,
        "capture",
        capture,
        &[&[0x1a], indy.as_slice(), &[0x84, 0, 1, 0xb0]].concat(),
    );
    class.method(
        0x100a,
        "lambda$capture$1",
        "(II)I",
        &[0x1a, 0x1b, 0x60, 0xac],
    );

    let text = class.source();
    assert!(
        text.contains("Runnable & Cloneable & Serializable"),
        "{text}"
    );
    assert!(text.contains("-> stack1 + "), "{text}");
    assert!(!text.contains("lambda$"), "{text}");
}

#[test]
fn retains_only_the_exact_fallback_helper_without_a_generated_name_collision() {
    let mut class = Class::default();
    let helper = class.handle(6, SAMPLE, "lambda$factory$0", "(I)I");
    let factory = "(I)Ljava/util/function/IntSupplier;";
    let indy = class.lambda(helper, "getAsInt", factory, "()I", "()I", None);
    class.method(
        9,
        "factory",
        factory,
        &[&[0x1a], indy.as_slice(), &[0xb0]].concat(),
    );
    // This bytecode writes its input slot. The captured variable is a lexical
    // final in Java, so the body needs a separately named retained method.
    class.method(
        0x100a,
        "lambda$factory$0",
        "(I)I",
        &[0x84, 0, 1, 0x1a, 0xac],
    );
    class.method(0x100a, "lambda$factory$0", "(J)J", &[0x1e, 0xad]);
    let text = class.source();
    assert!(
        text.contains("-> DynamicSites._lambda$factory$0("),
        "{text}"
    );
    assert!(text.contains("int _lambda$factory$0("), "{text}");
    assert!(!text.contains("long _lambda$factory$0("), "{text}");
}

#[test]
fn lowers_only_representable_constant_bootstraps() {
    let mut class = Class::default();
    let null = class.constant(
        "nullConstant",
        ")Ljava/lang/Object;",
        &[],
        "ignored",
        "Ljava/lang/String;",
    );
    class.method(
        9,
        "nil",
        "()Ljava/lang/String;",
        &[null.as_slice(), &[0xb0]].concat(),
    );
    let primitive = class.constant(
        "primitiveClass",
        ")Ljava/lang/Class;",
        &[],
        "V",
        "Ljava/lang/Class;",
    );
    class.method(
        9,
        "type",
        "()Ljava/lang/Class;",
        &[primitive.as_slice(), &[0xb0]].concat(),
    );
    let item = class.constant(
        "enumConstant",
        ")Ljava/lang/Enum;",
        &[],
        "APPEND",
        "Ljava/nio/file/StandardOpenOption;",
    );
    class.method(
        9,
        "item",
        "()Ljava/nio/file/StandardOpenOption;",
        &[item.as_slice(), &[0xb0]].concat(),
    );
    let value = class.entry(3, &257i32.to_be_bytes());
    let cast = class.constant(
        "explicitCast",
        "Ljava/lang/Object;)Ljava/lang/Object;",
        &[value],
        "ignored",
        "B",
    );
    class.method(9, "narrow", "()B", &[cast.as_slice(), &[0xac]].concat());
    let mut cast = class.constant(
        "explicitCast",
        "Ljava/lang/Object;)Ljava/lang/Object;",
        &[value],
        "ignored",
        "J",
    );
    cast[0] = 0x14; // ldc2_w
    class.method(9, "wide", "()J", &[cast.as_slice(), &[0xad]].concat());
    let text = class.source();
    for source in [
        "return null;",
        "return void.class;",
        "StandardOpenOption.APPEND;",
        "return (byte)(257);",
        "return (long)(257);",
    ] {
        assert!(text.contains(source), "missing {source}: {text}");
    }

    let mut class = Class::default();
    let array = class.class("[I");
    let cache = class.constant(
        "arrayVarHandle",
        "Ljava/lang/Class;)Ljava/lang/invoke/VarHandle;",
        &[array],
        "unused",
        "Ljava/lang/invoke/VarHandle;",
    );
    class.method(
        9,
        "array",
        "()Ljava/lang/invoke/VarHandle;",
        &[cache.as_slice(), &[0xb0]].concat(),
    );
    let error = decompile(&class.finish(), &Options::default()).unwrap_err();
    assert!(
        format!("{error:#?}").contains("lazy, cached JVM linkage"),
        "{error:#?}"
    );
}

const VAR_HANDLE: &str = "Ljava/lang/invoke/VarHandle;";
const FIELD_BOOTSTRAP_SUFFIX: &str =
    "Ljava/lang/Class;Ljava/lang/Class;)Ljava/lang/invoke/VarHandle;";
const ARRAY_BOOTSTRAP_SUFFIX: &str = "Ljava/lang/Class;)Ljava/lang/invoke/VarHandle;";

fn add_handle_method(class: &mut Class, name: &str, load: [u8; 3]) {
    let [op, high, low] = load;
    class.method(
        9,
        name,
        "()Ljava/lang/invoke/VarHandle;",
        &[op, high, low, 0xb0],
    );
}

#[test]
fn lowers_verified_var_handles_only_after_opt_in() {
    let mut class = Class::default();
    let point = class.class("java/awt/Point");
    let [_, high, low] = class.constant(
        "primitiveClass",
        ")Ljava/lang/Class;",
        &[],
        "I",
        "Ljava/lang/Class;",
    );
    let int = u16::from_be_bytes([high, low]);
    let load = class.constant(
        "fieldVarHandle",
        FIELD_BOOTSTRAP_SUFFIX,
        &[point, int],
        "x",
        VAR_HANDLE,
    );
    add_handle_method(&mut class, "x", load);

    let system = class.class("java/lang/System");
    let stream = class.class("java/io/PrintStream");
    let load = class.constant(
        "staticFieldVarHandle",
        FIELD_BOOTSTRAP_SUFFIX,
        &[system, stream],
        "out",
        VAR_HANDLE,
    );
    add_handle_method(&mut class, "out", load);

    let strings = class.class("[Ljava/lang/String;");
    let load = class.constant(
        "arrayVarHandle",
        ARRAY_BOOTSTRAP_SUFFIX,
        &[strings],
        "unused",
        VAR_HANDLE,
    );
    add_handle_method(&mut class, "strings", load);

    let bytes = class.finish();
    assert!(decompile(&bytes, &Options::default()).is_err());
    let mut options = Options::default();
    options
        .set("decompile-complex-constant-dynamic", "1")
        .unwrap();
    let text = decompile(&bytes, &options).unwrap().text;
    assert_eq!(
        text.matches("/* $VF: constant dynamic replaced with non-lazy method call */")
            .count(),
        3
    );
    // Calls may wrap once the warning pushes them beyond the preferred width.
    let flat = text.split_whitespace().collect::<Vec<_>>().join(" ");
    let flat = flat.replace("( ", "(").replace(" )", ")");
    for call in [
        "ConstantBootstraps.fieldVarHandle(MethodHandles.lookup(), \"x\", VarHandle.class, Point.class, int.class)",
        "ConstantBootstraps.staticFieldVarHandle(MethodHandles.lookup(), \"out\", VarHandle.class, System.class, PrintStream.class)",
        "MethodHandles.arrayElementVarHandle(String[].class)",
    ] {
        assert!(flat.contains(call), "{text}");
    }
}

#[test]
fn rejects_malformed_bootstraps_even_after_opt_in() {
    let mut options = Options::default();
    options
        .set("decompile-complex-constant-dynamic", "1")
        .unwrap();
    for (bootstrap, suffix, target, expected) in [
        (
            "arrayVarHandle",
            "Ljava/lang/Class;)Ljava/lang/Object;",
            "[I",
            "descriptor or arity",
        ),
        (
            "arrayVarHandle",
            ARRAY_BOOTSTRAP_SUFFIX,
            "java/lang/String",
            "needs an array class",
        ),
        (
            "fieldVarHandle",
            FIELD_BOOTSTRAP_SUFFIX,
            "[I",
            "descriptor or arity",
        ),
    ] {
        let mut class = Class::default();
        let target = class.class(target);
        let load = class.constant(bootstrap, suffix, &[target], "x", VAR_HANDLE);
        add_handle_method(&mut class, "broken", load);
        let error = decompile(&class.finish(), &options).unwrap_err();
        assert!(format!("{error:#?}").contains(expected), "{error:#?}");
    }

    let mut class = Class::default();
    let owner = class.class("java/awt/Point");
    let [_, hi, lo] = class.constant(
        "nullConstant",
        ")Ljava/lang/Object;",
        &[],
        "ignored",
        "Ljava/lang/Class;",
    );
    let not_primitive = u16::from_be_bytes([hi, lo]);
    let load = class.constant(
        "fieldVarHandle",
        FIELD_BOOTSTRAP_SUFFIX,
        &[owner, not_primitive],
        "x",
        VAR_HANDLE,
    );
    add_handle_method(&mut class, "broken", load);
    let error = decompile(&class.finish(), &options).unwrap_err();
    assert!(
        format!("{error:#?}").contains("not a verified primitiveClass"),
        "{error:#?}"
    );
}

#[test]
fn renders_primitive_sam_as_a_typed_anonymous_method() {
    let mut class = Class::default();
    let helper = class.handle(6, SAMPLE, "lambda$operator$0", "(I)I");
    let factory = "()Ljava/util/function/IntUnaryOperator;";
    let indy = class.lambda(helper, "applyAsInt", factory, "(I)I", "(I)I", None);
    class.method(9, "operator", factory, &[indy.as_slice(), &[0xb0]].concat());
    class.method(0x100a, "lambda$operator$0", "(I)I", &[0x1a, 0x04, 0x60, 0xac]);
    let mut options = Options::default();
    options.set("lambda-to-anonymous-class", "1").unwrap();
    let source = decompile(&class.finish(), &options).unwrap().text;
    assert!(source.contains("new IntUnaryOperator() {"), "{source}");
    assert!(source.contains("public int applyAsInt(int "), "{source}");
    assert!(source.contains(" + 1;"), "{source}");
    assert!(!source.contains("->") && !source.contains("lambda$"), "{source}");
}

#[test]
fn renders_parameterized_method_references_with_their_lexical_receiver() {
    let mut class = Class::default();
    let owner_type = "Lexample/DynamicSites;";
    let handle = class.handle(5, SAMPLE, "size", "()I");
    let factory = format!("({owner_type})Ljava/util/function/Supplier;");
    let indy = class.lambda(
        handle, "get", &factory, "()Ljava/lang/Object;", "()Ljava/lang/Integer;", None,
    );
    class.method(1, "supplier", "()Ljava/util/function/Supplier;", &[&[0x2a], indy.as_slice(), &[0xb0]].concat());
    class.method(1, "size", "()I", &[0x04, 0xac]);
    let mut options = Options::default();
    options.set("lambda-to-anonymous-class", "true").unwrap();
    let source = decompile(&class.finish(), &options).unwrap().text;
    assert!(source.contains("new Supplier<Integer>() {"), "{source}");
    assert!(source.contains("public Integer get()"), "{source}");
    assert!(source.contains("DynamicSites.this.size()"), "{source}");
    assert!(!source.contains("::"), "{source}");
}

#[test]
fn rejects_intersection_lambdas_that_an_anonymous_class_cannot_implement() {
    let mut class = Class::default();
    let helper = class.handle(6, SAMPLE, "lambda$factory$0", "()V");
    let flags = class.entry(3, &2i32.to_be_bytes());
    let one = class.entry(3, &1i32.to_be_bytes());
    let marker = class.class("java/lang/Cloneable");
    let factory = "()Ljava/lang/Runnable;";
    let indy = class.lambda(helper, "run", factory, "()V", "()V", Some(&[flags, one, marker]));
    class.method(9, "factory", factory, &[indy.as_slice(), &[0xb0]].concat());
    class.method(0x100a, "lambda$factory$0", "()V", &[0xb1]);
    let mut options = Options::default();
    options.lambda_to_anonymous_class = true;
    let error = decompile(&class.finish(), &options).unwrap_err();
    assert!(format!("{error:#?}").contains("additional interfaces"), "{error:#?}");
}
