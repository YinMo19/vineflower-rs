use std::io::{Cursor, Write};
use std::sync::atomic::{AtomicUsize, Ordering};

use tempfile::tempdir;
use zip::{CompressionMethod, ZipWriter, write::SimpleFileOptions};

use super::*;

const SAMPLE: &str = "example/Tiny";
const SAMPLE_FILE: &str = "example/Tiny.class";

fn class_bytes(name: &str, super_name: &str) -> Vec<u8> {
    fn words(bytes: &mut Vec<u8>, values: &[u16]) {
        for value in values {
            bytes.extend(value.to_be_bytes());
        }
    }
    fn text(bytes: &mut Vec<u8>, value: &str) {
        bytes.push(1); // CONSTANT_Utf8
        words(bytes, &[value.len().try_into().unwrap()]);
        bytes.extend(value.as_bytes());
    }
    let mut bytes = vec![0xCA, 0xFE, 0xBA, 0xBE];
    words(&mut bytes, &[0, 52, 15]);
    for (index, name) in [(1, name), (3, super_name), (5, "example/Face")] {
        text(&mut bytes, name);
        bytes.push(7); // CONSTANT_Class
        words(&mut bytes, &[index]);
    }
    for value in [
        "value",
        "Ljava/lang/Object;",
        "get",
        "()Ljava/lang/Object;",
        "Signature",
        "TT;",
        "()TT;",
        "<T:Ljava/lang/Object;>Ljava/lang/Object;Lexample/Face;",
    ] {
        text(&mut bytes, value);
    }
    words(&mut bytes, &[0x0421, 2, 4, 1, 6]); // class and interfaces
    words(&mut bytes, &[1, 0x0004, 7, 8, 1, 11, 0, 2, 12]); // field
    words(&mut bytes, &[1, 0x0401, 9, 10, 1, 11, 0, 2, 13]); // method
    words(&mut bytes, &[1, 11, 0, 2, 14]); // class signature
    bytes
}

fn write_archive(path: &Path, prefix: &[u8], entries: &[(&str, &[u8])]) {
    let mut zip = ZipWriter::new(Cursor::new(Vec::new()));
    let options = SimpleFileOptions::default().compression_method(CompressionMethod::Deflated);
    for &(name, bytes) in entries {
        zip.start_file(name, options).unwrap();
        zip.write_all(bytes).unwrap();
    }
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    let mut file = fs::File::create(path).unwrap();
    file.write_all(prefix).unwrap();
    file.write_all(&zip.finish().unwrap().into_inner()).unwrap();
}

#[test]
fn archive_is_lazy_and_names_are_exact() {
    let dir = tempdir().unwrap();
    let archive = dir.path().join("library.jar");
    let bytes = class_bytes(SAMPLE, "java/lang/Object");
    write_archive(
        &archive,
        &[],
        &[
            (SAMPLE_FILE, &bytes),
            ("example/Broken.class", b"broken body"),
            ("example/WrongName.class", &bytes),
            ("META-INF/versions/21/example/Versioned.class", b"not a base entry"),
        ],
    );
    let mut cp = ClassPath::new();
    cp.add(archive).unwrap();
    assert_eq!(cp.load(SAMPLE).unwrap().unwrap().as_ref(), bytes);
    for absent in ["example/tiny", "example/Absent", "example/Versioned", "META-INF/versions/21/example/Versioned"] {
        assert!(cp.load(absent).unwrap().is_none());
    }
    assert!(matches!(cp.load("example/Broken"), Err(ClassPathError::InvalidClass { .. })));
    assert!(matches!(cp.load("example/WrongName"), Err(ClassPathError::WrongClassName { .. })));

    let metadata = cp.metadata(SAMPLE).unwrap().unwrap();
    assert_eq!(metadata.name, SAMPLE);
    assert_eq!(metadata.super_name.as_deref(), Some("java/lang/Object"));
    assert_eq!(metadata.interfaces, ["example/Face"]);
    assert_eq!(metadata.access_flags, 0x0421);
    assert!(metadata.signature.as_deref().unwrap().starts_with("<T:"));
    assert_eq!(metadata.fields[0].descriptor, "Ljava/lang/Object;");
    assert_eq!(metadata.fields[0].signature.as_deref(), Some("TT;"));
    assert_eq!(metadata.methods[0].name, "get");
    assert_eq!(metadata.methods[0].descriptor, "()Ljava/lang/Object;");
    assert_eq!(metadata.methods[0].signature.as_deref(), Some("()TT;"));
    assert_eq!(metadata.methods[0].access_flags, 0x0401);
    assert!(Arc::ptr_eq(&metadata, &cp.metadata(SAMPLE).unwrap().unwrap()));
}

#[test]
fn directory_and_archive_use_insertion_order() {
    let dir = tempdir().unwrap();
    let root = dir.path().join("classes");
    fs::create_dir_all(root.join("example")).unwrap();
    let bytes = class_bytes(SAMPLE, "example/First");
    fs::write(root.join(SAMPLE_FILE), bytes).unwrap();
    let archive = dir.path().join("later.jar");
    let bytes = class_bytes(SAMPLE, "example/Second");
    write_archive(&archive, &[], &[(SAMPLE_FILE, &bytes)]);

    let mut cp = ClassPath::new();
    cp.add(&root).unwrap();
    cp.add(&archive).unwrap();
    let first = cp.metadata(SAMPLE).unwrap().unwrap();
    assert_eq!(first.super_name.as_deref(), Some("example/First"));
    for invalid in ["", "/example/Tiny", "example//Tiny", "example/../Tiny", "example/Tiny.class", "[Lexample/Tiny;", "C:\\Tiny", "example\0/Tiny"] {
        assert!(matches!(cp.load(invalid), Err(ClassPathError::InvalidName { .. })));
    }

    let mut cp = ClassPath::new();
    cp.add(&archive).unwrap();
    cp.add(&root).unwrap();
    assert_eq!(cp.load(SAMPLE).unwrap().unwrap().as_ref(), bytes);
}

#[cfg(unix)]
#[test]
fn directory_does_not_follow_paths_outside_its_root() {
    use std::os::unix::fs::symlink;

    let dir = tempdir().unwrap();
    let root = dir.path().join("classes");
    fs::create_dir(&root).unwrap();
    fs::write(dir.path().join("Tiny.class"), class_bytes(SAMPLE, "java/lang/Object")).unwrap();
    symlink(dir.path(), root.join("example")).unwrap();
    let mut cp = ClassPath::new();
    cp.add(root).unwrap();
    assert!(matches!(cp.load(SAMPLE), Err(ClassPathError::OutsideDirectory { .. })));
}

#[test]
fn java_8_home_or_jre_root() {
    for lib in ["jre/lib", "lib"] {
        let home = tempdir().unwrap();
        assert!(matches!(ClassPath::for_java_home(home.path()), Err(ClassPathError::RuntimeNotFound { .. })));
        let rt = class_bytes(SAMPLE, "java/lang/Object");
        let sibling = class_bytes("example/Extra", "java/lang/Object");
        write_archive(&home.path().join(lib).join("rt.jar"), &[], &[(SAMPLE_FILE, &rt)]);
        write_archive(&home.path().join(lib).join("first.jar"), &[], &[(SAMPLE_FILE, b"not the runtime class"), ("example/Extra.class", &sibling)]);
        let cp = ClassPath::for_java_home(home.path()).unwrap();
        assert_eq!(cp.load(SAMPLE).unwrap().unwrap().as_ref(), rt);
        assert_eq!(cp.load("example/Extra").unwrap().unwrap().as_ref(), sibling);
    }
}

#[test]
fn standalone_jmods_use_the_classes_namespace() {
    let home = tempdir().unwrap();
    let jmod = home.path().join("jmods/java.base.jmod");
    let bytes = class_bytes(SAMPLE, "java/lang/Object");
    write_archive(
        &jmod,
        b"JM\x01\x00",
        &[("classes/example/Tiny.class", &bytes), ("example/Tiny.class", b"not a class"), ("bin/Hidden.class", &bytes)],
    );
    let cp = ClassPath::for_java_home(home.path()).unwrap();
    assert_eq!(cp.load(SAMPLE).unwrap().unwrap().as_ref(), bytes);
    assert!(cp.load("bin/Hidden").unwrap().is_none());
    let bad = home.path().join("bad.jmod");
    write_archive(&bad, &[], &[]);
    assert!(matches!(ClassPath::new().add(bad), Err(ClassPathError::InvalidJmod { .. })));
}

#[test]
fn providers_are_lazy_and_share_bytes() {
    #[derive(Debug)]
    struct Provider {
        bytes: Arc<[u8]>,
        calls: Arc<AtomicUsize>,
    }
    impl ClassDataProvider for Provider {
        fn load(&self, name: &str) -> io::Result<Option<Arc<[u8]>>> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            match name {
                SAMPLE => Ok(Some(self.bytes.clone())),
                "example/Unreadable" => Err(io::Error::other("cannot read")),
                _ => Ok(None),
            }
        }
    }
    let bytes: Arc<[u8]> = class_bytes(SAMPLE, "java/lang/Object").into();
    let calls = Arc::new(AtomicUsize::new(0));
    let mut cp = ClassPath::new();
    cp.add_provider(Provider { bytes: bytes.clone(), calls: calls.clone() });
    let dir = tempdir().unwrap();
    let later = dir.path().join("later.jar");
    write_archive(&later, &[], &[(SAMPLE_FILE, b"not the provider class")]);
    cp.add(later).unwrap();
    assert_eq!(calls.load(Ordering::Relaxed), 0);
    assert!(Arc::ptr_eq(&bytes, &cp.load(SAMPLE).unwrap().unwrap()));
    assert!(cp.metadata(SAMPLE).unwrap().is_some());
    assert_eq!(calls.load(Ordering::Relaxed), 1);
    assert!(cp.load("example/Missing").unwrap().is_none());
    assert!(matches!(cp.load("example/Unreadable"), Err(ClassPathError::Provider { .. })));
}

fn write_image(home: &Path, bytes: &[u8], compression: Option<(&str, &[u8])>) {
    let mut strings = b"\0java.base\0example\0Tiny\0class\0".to_vec();
    let mut attr = vec![0, 8, 1, 16, 11, 24, 19, 32, 24];
    let mut data = Vec::new();
    if let Some((algorithm, payload)) = compression {
        data.extend(0xCAFE_FAFAu32.to_le_bytes());
        data.extend((payload.len() as u64).to_le_bytes());
        data.extend((bytes.len() as u64).to_le_bytes());
        data.extend((strings.len() as u32).to_le_bytes());
        data.extend(u32::MAX.to_le_bytes());
        data.push(1);
        data.extend(payload);
        strings.extend(algorithm.as_bytes());
        strings.push(0);
        attr.push((6 << 3) | 1);
        attr.extend((data.len() as u16).to_be_bytes());
    } else {
        data.extend(bytes);
    }
    attr.push((7 << 3) | 1);
    attr.extend((bytes.len() as u16).to_be_bytes());
    attr.push(0);
    let mut image = Vec::new();
    for n in [0xCAFE_DADA, 0x0001_0000, 0, 1, 1, attr.len() as u32, strings.len() as u32, u32::MAX, 1] {
        image.extend(n.to_le_bytes());
    }
    image.extend(attr);
    image.extend(strings);
    image.extend(data);
    fs::create_dir_all(home.join("lib")).unwrap();
    fs::write(home.join("lib/modules"), image).unwrap();
}

fn zlib_stored(bytes: &[u8]) -> Vec<u8> {
    let len = u16::try_from(bytes.len()).unwrap();
    let mut stream = vec![0x78, 0x01, 0x01]; // zlib header, final stored DEFLATE block
    stream.extend(len.to_le_bytes());
    stream.extend((!len).to_le_bytes());
    stream.extend(bytes);
    let (a, b) = bytes.iter().fold((1, 0), |(a, b), &byte| {
        let a = (a + u32::from(byte)) % 65521;
        (a, (b + a) % 65521)
    });
    stream.extend(((b << 16) | a).to_be_bytes());
    stream
}

#[test]
fn runtime_image_resources_are_loaded_and_decompressed_on_demand() {
    let bytes = class_bytes(SAMPLE, "java/lang/Object");
    let zlib = zlib_stored(&bytes);
    for compression in [None, Some(("zip", zlib.as_slice())), Some(("compact-cp", b"".as_slice()))] {
        let home = tempdir().unwrap();
        write_image(home.path(), &bytes, compression);
        let cp = ClassPath::for_java_home(home.path()).unwrap();
        assert!(cp.load("example/Absent").unwrap().is_none());
        if compression.is_some_and(|(algorithm, _)| algorithm == "compact-cp") {
            assert!(matches!(cp.load(SAMPLE), Err(ClassPathError::UnsupportedImageCompression { algorithm, .. }) if algorithm == "compact-cp"));
        } else {
            assert_eq!(cp.load(SAMPLE).unwrap().unwrap().as_ref(), bytes);
        }
    }
}

#[test]
fn selected_installed_runtime_when_available() {
    let Some(home) = std::env::var_os("JAVA_HOME").map(PathBuf::from) else { return };
    let cp = match ClassPath::for_java_home(&home) {
        Ok(cp) => cp,
        Err(ClassPathError::RuntimeNotFound { .. }) => return,
        Err(other) => panic!("{other}"),
    };
    let object = match cp.metadata("java/lang/Object") {
        Ok(Some(object)) => object,
        Err(ClassPathError::UnsupportedImageCompression { .. }) => return,
        other => panic!("expected java/lang/Object metadata from {home:?}, got {other:?}"),
    };
    assert_eq!(object.name, "java/lang/Object");
    assert!(object.super_name.is_none());
    assert!(object.methods.iter().any(|m| m.name == "hashCode" && m.descriptor == "()I"));
    assert!(cp.load("java/lang/DoesNotExistVineflower").unwrap().is_none());
    assert_eq!(cp.metadata("java/lang/String").unwrap().unwrap().super_name.as_deref(), Some("java/lang/Object"));

    let jmod = home.join("jmods/java.base.jmod");
    if jmod.is_file() {
        let mut jmods = ClassPath::new();
        jmods.add(jmod).unwrap();
        assert_eq!(jmods.metadata("java/lang/Object").unwrap().unwrap().as_ref(), object.as_ref());
    }
}
