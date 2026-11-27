use std::env;
use std::fmt::Write as _;
use std::io::{Seek as _, Write as _};
use std::path::{Path, PathBuf};
use std::process::Command;

use vineflower_rs::util::java_str::JavaString;
use vineflower_rs::util::jhash::{JHashMap, JHashSet, JavaHash};

#[test]
fn ordered_values_and_borrowed_keys_survive_tree_removals() {
    let mut map = JHashMap::with_capacity(64);
    let keys: Vec<String> = (0..16)
        .map(|index| {
            (0..4)
                .map(|bit| if index & (1 << bit) == 0 { "Aa" } else { "BB" })
                .collect()
        })
        .collect();
    for (value, key) in keys.iter().enumerate() {
        map.insert(key.clone(), value);
    }
    assert_eq!(map.remove(keys[3].as_str()), Some(3));
    assert!(map.contains_key(keys[15].as_str()));
    assert_eq!(*map.get_mut(keys[15].as_str()).unwrap(), 15);

    map.retain(|_, value| *value % 3 != 0);
    let values: Vec<_> = map.values_mut().map(|value| *value).collect();
    assert_eq!(
        values,
        (0..16).filter(|value| value % 3 != 0).collect::<Vec<_>>()
    );
    assert!(map.iter().eq(map.clone().iter()));
    map.clear();
    assert!(map.iter().next().is_none());
    map.insert(keys[3].clone(), 23);
    assert_eq!(map.get(keys[3].as_str()), Some(&23));
}

#[test]
fn set_remove_all_follows_the_two_abstract_set_paths() {
    let mut set = JHashSet::with_capacity(64);
    set.extend((0..13).map(|index| index * 128));
    let key = *set.iter().next().unwrap();

    let mut expected = set.clone();
    expected.remove(&key);
    let small = JHashSet::from_collection([key], 1);
    let mut direct = set.clone();
    direct.remove_all(&small);
    assert!(direct.iter().eq(expected.iter()));

    let mut large = JHashSet::with_capacity(64);
    large.extend(1..=set.len() as i32 + 1);
    large.insert(key);
    let mut iterated = set.clone();
    iterated.remove_all(&large);
    assert!(
        iterated
            .iter()
            .eq(set.iter().filter(|&&value| value != key))
    );
    assert_eq!(direct, iterated);
    assert!(!direct.iter().eq(iterated.iter()));
}

#[test]
#[ignore = "requires an OpenJDK 17 installation"]
fn tree_bins_match_openjdk_17() {
    let mut trace = Trace::default();
    integers(&mut trace);
    for (low, high) in [(11, 11), (9, 5), (5, 9), (6, 6), (15, 0), (0, 15)] {
        split(&mut trace, low, high);
    }
    longs(&mut trace);
    strings(&mut trace);

    let java = env::var_os("VINEFLOWER_JDK_17")
        .or_else(|| env::var_os("JAVA_HOME"))
        .map(PathBuf::from)
        .map(|home| {
            home.join("bin")
                .join(format!("java{}", env::consts::EXE_SUFFIX))
        })
        .unwrap_or_else(|| PathBuf::from("java"));
    let version = Command::new(&java).arg("-version").output().unwrap();
    assert!(version.status.success());
    assert!(
        String::from_utf8_lossy(&version.stderr).contains("version \"17."),
        "expected JDK 17 at {java:?}, got {}",
        String::from_utf8_lossy(&version.stderr)
    );
    let mut input = tempfile::tempfile().unwrap();
    input.write_all(trace.input.as_bytes()).unwrap();
    input.rewind().unwrap();
    let reference =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("test/support/HashMapReference.java");
    let result = Command::new(java)
        .arg("--add-opens=java.base/java.util=ALL-UNNAMED")
        .arg(reference)
        .stdin(input)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let actual = String::from_utf8(result.stdout).unwrap();
    let mut rows = actual.lines();
    for (index, expected) in trace.rows.iter().enumerate() {
        let row = rows.next().unwrap();
        assert_eq!(
            expected,
            row,
            "after {}",
            trace.input.lines().nth(index).unwrap()
        );
    }
    assert!(rows.next().is_none());
    eprintln!(
        "Compared {} map operations. {}",
        trace.rows.len(),
        String::from_utf8_lossy(&result.stderr).trim()
    );
}

fn integers(trace: &mut Trace) {
    let mut case = trace.case("int", None, i32::to_string);
    let keys: Vec<_> = (-41i32..42).map(|index| unspread(index * 256)).collect();
    for (value, &key) in keys.iter().enumerate().take(16) {
        case.put(key, value as i32);
    }
    case.retain(4, 0);
    case.put(keys[17], 30);
    case.copy("clone");
    for &key in keys.iter().take(25).rev() {
        case.remove(key);
    }
    exercise(&mut case, &keys);

    // Put-only treeification at 9 nodes and compute-only treeification at 8.
    let mut case = trace.case("int", Some(64), i32::to_string);
    for (value, &key) in keys.iter().enumerate().take(9) {
        case.compute(key, value as i32);
    }
    // The first inserted key in this order isn't required to be the root.
    // Keep one entry via the iterator, then expand and insert into its bin.
    case.retain(2, 1);
    case.retain(3, 0);
    case.retain(3, 2);
    case.put_all((1..=110).map(|key| (key, key)).collect());
    case.put(keys[30], 1024);
    case.clear();
}

fn split(trace: &mut Trace, low: i32, high: i32) {
    let mut case = trace.case("int", Some(64), i32::to_string);
    for i in 0..low.max(high) {
        if i < low {
            case.put(unspread((i - 7) * 128), i);
        }
        if i < high {
            case.put(unspread((i - 7) * 128 + 64), i);
        }
    }
    for key in 1..=(49 - low - high) {
        case.put(key, key);
    }
    case.compute(unspread(17 * 128), 101);
    case.compute(unspread(19 * 128 + 64), 102);
    case.remove(unspread(-3 * 128));
    case.remove(unspread(-5 * 128 + 64));
    case.retain(3, 1);
}

fn longs(trace: &mut Trace) {
    let encode = |key: &Option<i64>| key.map_or_else(|| "~".into(), |key| key.to_string());
    let mut case = trace.case("long", Some(64), encode);
    let mut keys = vec![None];
    for index in 0..64 {
        let upper = (index * 37 % 64) - 32;
        let value = |hash| i64::from(upper) << 32 | i64::from((upper ^ hash) as u32);
        keys.push(Some(value(0)));
        keys.push(Some(value(i32::MIN)));
    }
    for (value, &key) in keys.iter().enumerate().take(28) {
        case.put(key, value as i32);
    }
    case.copy("copy");
    case.retain(3, 0);
    exercise(&mut case, &keys);
}

fn strings(trace: &mut Trace) {
    let (supplementary, bmp) = ([0xdbff, 0xdfff], [0xe000, 0xdfff - 0x401 * 31]);
    let mut keys = Vec::new();
    for index in 0..32 {
        let units: Vec<u16> = (0..5)
            .flat_map(|bit| {
                if index & (1 << bit) == 0 {
                    supplementary
                } else {
                    bmp
                }
            })
            .collect();
        keys.push(String::from_utf16(&units).unwrap());
    }
    assert!(
        keys.iter()
            .all(|key| key.java_hash() == keys[0].java_hash())
    );
    let encode = |key: &String| {
        key.encode_utf16()
            .map(|unit| format!("{unit:04x}"))
            .collect()
    };
    let mut case = trace.case("text", Some(64), encode);
    for (value, key) in keys.iter().cloned().rev().enumerate() {
        case.compute(key, value as i32);
    }
    exercise(&mut case, &keys);

    let mut keys: Vec<_> = keys.into_iter().map(JavaString::from).collect();
    let unpaired = [0xdc00, 0xdfff - 31];
    for index in 0..16 {
        let units = (0..5)
            .flat_map(|bit| {
                if index & (1 << bit) == 0 {
                    unpaired
                } else {
                    bmp
                }
            })
            .collect();
        keys.push(JavaString::from_utf16(units));
    }
    assert!(
        keys.iter()
            .all(|key| key.java_hash() == keys[0].java_hash())
    );
    let encode = |key: &JavaString| key.utf16().map(|unit| format!("{unit:04x}")).collect();
    let mut case = trace.case("text", Some(64), encode);
    for (value, key) in keys.iter().cloned().enumerate() {
        case.put(key, value as i32);
    }
    exercise(&mut case, &keys);
}

fn exercise<K>(case: &mut Case<'_, K>, keys: &[K])
where
    K: JavaHash + std::hash::Hash + Eq + Clone,
{
    let mut random: u32 = 3;
    for value in 0..600 {
        random = random.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        let key = keys[(random >> 13) as usize % keys.len()].clone();
        match random % 128 {
            0 => case.copy("clone"),
            1 => case.copy("copy"),
            2 => case.retain(9, value % 9),
            3 => case.put_all(
                keys.iter()
                    .skip(1)
                    .take(75)
                    .cloned()
                    .enumerate()
                    .map(|(i, key)| (key, i as i32))
                    .collect(),
            ),
            4..=29 => case.remove(key),
            30..=40 => case.replace(key, value),
            41..=79 => case.compute(key, value),
            _ => case.put(key, value),
        }
    }
}

fn unspread(hash: i32) -> i32 {
    hash ^ (hash as u32 >> 16) as i32
}

#[derive(Default)]
struct Trace {
    input: String,
    rows: Vec<String>,
}

impl Trace {
    fn case<K>(
        &mut self,
        kind: &str,
        capacity: Option<usize>,
        encode: fn(&K) -> String,
    ) -> Case<'_, K>
    where
        K: JavaHash + std::hash::Hash + Eq + Clone,
    {
        let mut case = Case {
            trace: self,
            map: capacity.map_or_else(JHashMap::new, JHashMap::with_capacity),
            encode,
        };
        let capacity = capacity.map_or(-1, |capacity| capacity as i32);
        case.row(&format!("new {kind} {capacity}"), "-");
        case
    }
}

struct Case<'a, K> {
    trace: &'a mut Trace,
    map: JHashMap<K, i32>,
    encode: fn(&K) -> String,
}

impl<K: JavaHash + std::hash::Hash + Eq + Clone> Case<'_, K> {
    fn row(&mut self, command: &str, result: &str) {
        let step = self.trace.rows.len();
        writeln!(self.trace.input, "{step} {command}").unwrap();
        let mut row = format!("{step}\t{result}\t");
        for (index, (key, value)) in self.map.iter().enumerate() {
            if index != 0 {
                row.push(',');
            }
            write!(row, "{}={value}", (self.encode)(key)).unwrap();
            assert_eq!(self.map.get(key), Some(value));
        }
        self.trace.rows.push(row);
    }

    fn put(&mut self, key: K, value: i32) {
        let command = format!("put {} {value}", (self.encode)(&key));
        let result = self.map.insert(key, value);
        self.row(&command, &nullable(result));
    }

    fn put_all(&mut self, entries: Vec<(K, i32)>) {
        let mut command = "putAll".to_owned();
        for (key, value) in &entries {
            write!(command, " {} {value}", (self.encode)(key)).unwrap();
        }
        let len = entries.len();
        self.map.put_all(entries, len);
        self.row(&command, "-");
    }

    fn compute(&mut self, key: K, value: i32) {
        let command = format!("compute {} {value}", (self.encode)(&key));
        let result = *self.map.get_or_insert_with(key, || value);
        self.row(&command, &result.to_string());
    }

    fn replace(&mut self, key: K, value: i32) {
        let result = self
            .map
            .get_mut(&key)
            .map(|entry| std::mem::replace(entry, value));
        self.row(
            &format!("replace {} {value}", (self.encode)(&key)),
            &nullable(result),
        );
    }

    fn remove(&mut self, key: K) {
        let result = self.map.remove(&key);
        self.row(
            &format!("remove {}", (self.encode)(&key)),
            &nullable(result),
        );
    }

    fn retain(&mut self, divisor: i32, residue: i32) {
        let encode = self.encode;
        let mut order = Vec::new();
        self.map.retain(|key, value| {
            order.push(encode(key));
            value.rem_euclid(divisor) != residue
        });
        self.row(&format!("retain {divisor} {residue}"), &order.join(","));
    }

    fn copy(&mut self, command: &str) {
        self.map = JHashMap::copy_of(&self.map);
        self.row(command, "-");
    }

    fn clear(&mut self) {
        self.map.clear();
        self.row("clear", "-");
    }
}

fn nullable(value: Option<i32>) -> String {
    value.map_or_else(|| "-".into(), |value| value.to_string())
}
