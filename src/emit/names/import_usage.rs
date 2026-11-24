use std::collections::HashMap;

use unicode_general_category::{GeneralCategory, get_general_category};

/// Only an unqualified identifier can require a single-type import. Work on
/// the emitted body rather than the speculative expressions that chose its
/// spelling. Coincidental identifiers are kept; this is not name resolution.
/// Return false if tokenization is uncertain so all imports are retained.
pub(super) fn mark_used(source: &str, names: &mut HashMap<&str, bool>) -> bool {
    let mut chars = source.char_indices().peekable();
    let mut qualified = false;
    let mut remaining = names.len();
    while let Some((start, ch)) = chars.next() {
        match ch {
            '/' if chars.next_if(|&(_, next)| next == '/').is_some() => {
                while chars
                    .next_if(|&(_, next)| !matches!(next, '\r' | '\n'))
                    .is_some()
                {}
            }
            '/' if chars.next_if(|&(_, next)| next == '*').is_some() => loop {
                match chars.next() {
                    Some((_, '*')) if chars.next_if(|&(_, next)| next == '/').is_some() => break,
                    Some(_) => (),
                    None => return false,
                }
            },
            '"' | '\'' => {
                if source[start..].starts_with("\"\"\"") {
                    // Java string emission currently uses ordinary literals.
                    return false;
                }
                loop {
                    match chars.next() {
                        Some((_, '\\')) if chars.next().is_some() => (),
                        Some((_, end)) if end == ch => break,
                        Some((_, '\r' | '\n')) | None => return false,
                        Some(_) => (),
                    }
                }
                qualified = false;
            }
            '\\' => return false,
            '.' => qualified = true,
            c if c.is_whitespace() => (),
            c if identifier_part(c) => {
                while chars.next_if(|&(_, ch)| identifier_part(ch)).is_some() {}
                let end = chars.peek().map_or(source.len(), |&(end, _)| end);
                if !qualified && let Some(used @ false) = names.get_mut(&source[start..end]) {
                    *used = true;
                    remaining -= 1;
                    if remaining == 0 {
                        return true;
                    }
                }
                qualified = false;
            }
            _ => qualified = false,
        }
    }
    true
}

fn identifier_part(ch: char) -> bool {
    if ch.is_ascii() {
        return ch.is_ascii_alphanumeric() || matches!(ch, '$' | '_');
    }
    use GeneralCategory::*;
    matches!(
        get_general_category(ch),
        UppercaseLetter
            | LowercaseLetter
            | TitlecaseLetter
            | ModifierLetter
            | OtherLetter
            | LetterNumber
            | CurrencySymbol
            | ConnectorPunctuation
            | NonspacingMark
            | SpacingMark
            | DecimalNumber
            | Format
    )
}
