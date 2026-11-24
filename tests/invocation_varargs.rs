use vineflower_rs::{Options, decompile};

// The original java8 TestNumberDisambiguation fixture, compiled with debug info.
const CLASS: &[u8] = include_bytes!("smoke/java8/TestNumberDisambiguation.class");

#[test]
fn upstream_varargs_calls_preserve_the_int_and_float_descriptors() {
    let mut options = Options::default();
    options.include_line_mappings = true;
    let source = decompile(CLASS, &options).unwrap();
    let lines: Vec<_> = source.text.lines().collect();
    let map = source.map.unwrap();
    let method = map.methods.iter().find(|method| method.name == "test").unwrap();
    for (bytes, expected) in [
        (159..168, "this.varargs(i);"),
        (170..180, "this.varargs((float)i);"),
    ] {
        for byte in bytes {
            assert_eq!(lines[method.offsets[&byte]].trim(), expected, "byte {byte}");
        }
    }
}
