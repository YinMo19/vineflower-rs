use std::{env, fs, path::PathBuf, process::Command};

use vineflower_rs::{Options, classfile::ClassFile, decompile_group};

const OUTER: &[u8] = include_bytes!("smoke/java8nodebug/TestDoubleNestedClass.class");
const FIRST: &[u8] = include_bytes!("smoke/java8nodebug/TestDoubleNestedClass$1.class");
const LOCAL: &[u8] = include_bytes!("smoke/java8nodebug/TestDoubleNestedClass$1$1Local.class");
const SECOND: &[u8] = include_bytes!("smoke/java8nodebug/TestDoubleNestedClass$2.class");
const OBJECT: &[u8] = include_bytes!("smoke/java8nodebug/TestDoubleNestedClass$2$1.class");
const CHILD: &[u8] = include_bytes!("smoke/java8nodebug/TestDoubleNestedClass$Child1.class");
const LAMBDA_CLASS: &[u8] = include_bytes!("smoke/java8nodebug/TestDoubleNestedClass$Child1$1.class");

fn recovered() -> String {
    decompile_group(OUTER, [FIRST, LOCAL, SECOND, OBJECT, CHILD, LAMBDA_CLASS], &Options::default())
        .unwrap()
        .text
}

#[test]
fn anonymous_enclosing_field_uses_its_lexical_name() {
    let source = recovered();
    assert!(source.contains("class Local {"), "{source}");
    assert!(source.contains("return x;"), "{source}");
    assert!(source.contains("return new Object() {};"), "{source}");
    assert!(source.contains("() -> new TestDoubleNestedClass() {"), "{source}");
    assert!(source.contains("Child1.this.x"), "{source}");
    assert!(!source.contains("access$") && !source.contains("this$0"), "{source}");
}

#[test]
fn a_same_named_local_class_field_blocks_the_lexical_rewrite() {
    // The original accessor still reads the anonymous owner even when class-file
    // input adds a conflicting field on Local. A Java simple name cannot do so.
    let mut local = LOCAL.to_vec();
    let this_0 = [0, 1, 0x10, 0x10, 0, 6, 0, 9, 0, 0];
    let fields = local.windows(this_0.len()).position(|bytes| bytes == this_0).unwrap();
    let pool_end = fields - 8; // access flags, this_class, super_class, no interfaces
    let field_name = u16::from_be_bytes([local[8], local[9]]);
    let field_desc = field_name + 1;
    local[8..10].copy_from_slice(&(field_desc + 1).to_be_bytes());
    local[fields + 1] = 2;
    let [name_hi, name_lo] = field_name.to_be_bytes();
    let [desc_hi, desc_lo] = field_desc.to_be_bytes();
    let new_field = [0, 0, name_hi, name_lo, desc_hi, desc_lo, 0, 0];
    local.splice(fields + this_0.len()..fields + this_0.len(), new_field);
    local.splice(pool_end..pool_end, [1, 0, 1, b'x', 1, 0, 1, b'I']);
    let parsed = ClassFile::parse(&local).unwrap();
    assert_eq!(parsed.pool.utf8(parsed.fields[1].name_index).unwrap(), "x");
    let error = decompile_group(OUTER, [FIRST, local.as_slice(), SECOND, OBJECT, CHILD, LAMBDA_CLASS], &Options::default())
        .unwrap_err().to_string();
    assert!(error.contains("getX()I") && error.contains("offset 4")
        && error.contains("synthetic nest field is not nameable here"), "{error}");
}

#[test]
#[ignore = "requires VINEFLOWER_JDK_8 to compile the no-debug shadowing fixture"]
fn a_generated_enclosing_local_name_blocks_the_lexical_rewrite() {
    let jdk = PathBuf::from(env::var_os("VINEFLOWER_JDK_8").expect("set VINEFLOWER_JDK_8"));
    let work = tempfile::tempdir().unwrap();
    let path = work.path();
    let source = path.join("ShadowedOuter.java");
    fs::write(&source, r#"
package pkg;

public abstract class ShadowedOuter {
    abstract Object get();

    private static final ShadowedOuter INNER = new ShadowedOuter() {
        private int var1 = 5;

        Object get() {
            int ignored = Integer.parseInt("3");
            class Local {
                int getX() {
                    return var1;
                }
            }
            return new Local();
        }
    };
}
"#).unwrap();
    run(Command::new(jdk.join("bin/javac")).arg("-g:none").arg("-d").arg(path).arg(&source));
    let outer = fs::read(path.join("pkg/ShadowedOuter.class")).unwrap();
    let owner = fs::read(path.join("pkg/ShadowedOuter$1.class")).unwrap();
    let local = fs::read(path.join("pkg/ShadowedOuter$1$1Local.class")).unwrap();
    // `ignored` would be printed as `var1` without local debug information.
    // Inserting `return var1;` would silently capture that local, not the field.
    let error = decompile_group(&outer, [owner.as_slice(), local.as_slice()], &Options::default())
        .unwrap_err().to_string();
    assert!(error.contains("getX()I") && error.contains("offset 4")
        && error.contains("synthetic nest field is not nameable here"), "{error}");
}

#[test]
#[ignore = "requires VINEFLOWER_JDK_8 for the Java 8 source/runtime round trip"]
fn recompiled_nested_classes_read_the_same_live_fields_and_lexical_captures() {
    let jdk = PathBuf::from(env::var_os("VINEFLOWER_JDK_8").expect("set VINEFLOWER_JDK_8"));
    let javac = jdk.join("bin/javac");
    let java = jdk.join("bin/java");
    let work = tempfile::tempdir().unwrap();
    let original = work.path().join("original");
    let candidate = work.path().join("candidate");
    let runner_classes = work.path().join("runner");
    fs::create_dir_all(original.join("pkg")).unwrap();
    fs::create_dir(&candidate).unwrap();
    fs::create_dir(&runner_classes).unwrap();
    for bytes in [OUTER, FIRST, LOCAL, SECOND, OBJECT, CHILD, LAMBDA_CLASS] {
        let class = ClassFile::parse(bytes).unwrap();
        let name = class.pool.class_name(class.this_class).unwrap();
        fs::write(original.join(format!("{name}.class")), bytes).unwrap();
    }

    let source = work.path().join("TestDoubleNestedClass.java");
    fs::write(&source, recovered()).unwrap();
    run(Command::new(&javac).arg("-g:none").arg("-d").arg(&candidate).arg(&source));

    let runner = work.path().join("Runner.java");
    fs::write(&runner, r#"
package pkg;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.function.Supplier;

public class Runner {
    private static TestDoubleNestedClass inner(String name) throws Exception {
        Field field = TestDoubleNestedClass.class.getDeclaredField(name);
        field.setAccessible(true);
        return (TestDoubleNestedClass) field.get(null);
    }

    public static void main(String[] args) throws Exception {
        TestDoubleNestedClass first = inner("INNER1");
        Object local = first.test();
        Method getX = local.getClass().getDeclaredMethod("getX");
        System.out.println(getX.invoke(local));
        Field x = first.getClass().getDeclaredField("x");
        x.setAccessible(true);
        x.setInt(first, 41);
        System.out.println(getX.invoke(local));

        TestDoubleNestedClass second = inner("INNER2");
        Object value = second.test();
        System.out.println(value != second.test() && value.getClass() == second.test().getClass());
        System.out.println(value.getClass().isAnonymousClass());

        TestDoubleNestedClass.Child1 child = new TestDoubleNestedClass.Child1();
        Supplier<TestDoubleNestedClass> a = child.foo(7);
        Supplier<TestDoubleNestedClass> b = child.foo(2);
        child.x = 19;
        TestDoubleNestedClass instance = a.get();
        System.out.println(instance.test());
        child.x = -2;
        System.out.println(instance.test());
        System.out.println(b.get().test());
        System.out.println(a.get().getClass() == b.get().getClass());
    }
}
"#).unwrap();
    run(Command::new(&javac).arg("-cp").arg(&original).arg("-d").arg(&runner_classes).arg(&runner));
    for classes in [&original, &candidate] {
        let cp = env::join_paths([classes, &runner_classes]).unwrap();
        let result = run(Command::new(&java).arg("-cp").arg(cp).arg("pkg.Runner"));
        assert_eq!(String::from_utf8(result).unwrap().replace("\r\n", "\n"), "5\n41\ntrue\ntrue\n62\n20\n10\ntrue\n");
    }
}

fn run(command: &mut Command) -> Vec<u8> {
    let output = command.output().unwrap();
    assert!(output.status.success(), "{command:?}:\n{}", String::from_utf8_lossy(&output.stderr));
    output.stdout
}
