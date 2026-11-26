// SPDX-License-Identifier: Apache-2.0

//! Java ZIP savers write a parsed JAR manifest when the input has one.

use std::io;

use indexmap::IndexMap;

use crate::util::jhash::JHashMap;

type Attributes = IndexMap<String, (String, String)>;

pub(super) fn rewrite(input: &[u8]) -> io::Result<Vec<u8>> {
    let mut sections = logical_sections(input)?;
    let mut main = Attributes::new();
    add_attributes(&mut main, sections.next().unwrap_or_default())?;

    let mut entries = JHashMap::new();
    for section in sections.filter(|section| !section.is_empty()) {
        let mut lines = section.into_iter();
        let (kind, name) = field(&lines.next().unwrap())?;
        if !kind.eq_ignore_ascii_case("Name") {
            return Err(invalid_manifest(
                "Manifest entry section has no Name header",
            ));
        }
        if !entries.contains_key(&name) {
            entries.insert(name.clone(), Attributes::new());
        }
        add_attributes(entries.get_mut(&name).unwrap(), lines)?;
    }

    let mut output = Vec::new();
    if let Some((key, spelling)) = [
        ("MANIFEST-VERSION", "Manifest-Version"),
        ("SIGNATURE-VERSION", "Signature-Version"),
    ]
    .into_iter()
    .find(|(key, _)| main.contains_key(*key))
    {
        let (_, value) = main.shift_remove(key).unwrap();
        output.extend_from_slice(format!("{spelling}: {value}\r\n").as_bytes());
        write_attributes(&mut output, &main);
    } else {
        output.extend_from_slice(b"\r\n");
    }

    for (name, attributes) in entries.iter() {
        write_line(&mut output, &format!("Name: {name}"));
        write_attributes(&mut output, attributes);
    }
    Ok(output)
}

fn logical_sections(mut input: &[u8]) -> io::Result<impl Iterator<Item = Vec<Vec<u8>>>> {
    let mut sections = vec![Vec::<Vec<u8>>::new()];
    while let Some(end) = input.iter().position(|&byte| matches!(byte, b'\r' | b'\n')) {
        let line = &input[..end];
        let separator = if input[end..].starts_with(b"\r\n") {
            2
        } else {
            1
        };
        if end + separator > 512 {
            return Err(invalid_manifest("Manifest line is too long"));
        }
        input = &input[end + separator..];

        if line.is_empty() {
            sections.push(Vec::new());
        } else if let Some(continued) = line.strip_prefix(b" ") {
            let previous = sections
                .last_mut()
                .unwrap()
                .last_mut()
                .ok_or_else(|| invalid_manifest("Misplaced manifest continuation"))?;
            previous.extend_from_slice(continued);
        } else {
            sections.last_mut().unwrap().push(line.to_vec());
        }
    }
    if input.len() >= 512 {
        return Err(invalid_manifest("Manifest line is too long"));
    }
    Ok(sections.into_iter())
}

fn field(line: &[u8]) -> io::Result<(String, String)> {
    let Some(separator) = line.iter().position(|&byte| byte == b':') else {
        return Err(invalid_manifest("Manifest header has no colon"));
    };
    let name = &line[..separator];
    let value = line[separator + 1..]
        .strip_prefix(b" ")
        .ok_or_else(|| invalid_manifest("Manifest header has no separator space"))?;
    if !(1..=70).contains(&name.len())
        || !name
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
    {
        return Err(invalid_manifest("Invalid manifest attribute name"));
    }
    Ok((
        std::str::from_utf8(name).unwrap().to_owned(),
        String::from_utf8_lossy(value).into_owned(),
    ))
}

fn add_attributes(
    attrs: &mut Attributes,
    lines: impl IntoIterator<Item = Vec<u8>>,
) -> io::Result<()> {
    for line in lines {
        let (name, value) = field(&line)?;
        let key = name.to_ascii_uppercase();
        if let Some((_, previous)) = attrs.get_mut(&key) {
            log::warn!("Duplicate name in manifest: {name}");
            *previous = value;
        } else {
            attrs.insert(key, (name, value));
        }
    }
    Ok(())
}

fn write_attributes(output: &mut Vec<u8>, attrs: &Attributes) {
    for (name, value) in attrs.values() {
        write_line(output, &format!("{name}: {value}"));
    }
    output.extend_from_slice(b"\r\n");
}

fn write_line(output: &mut Vec<u8>, line: &str) {
    let bytes = line.as_bytes();
    let split = bytes.len().min(72);
    output.extend_from_slice(&bytes[..split]);
    for continued in bytes[split..].chunks(71) {
        output.extend_from_slice(b"\r\n ");
        output.extend_from_slice(continued);
    }
    output.extend_from_slice(b"\r\n");
}

fn invalid_manifest(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
