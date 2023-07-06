use std::fmt;

use crate::chars::*;

pub fn print_identifier(identifier: &str, w: &mut impl fmt::Write) -> fmt::Result {
    if must_be_quoted(identifier) {
        print_quoted(identifier, '"', w)
    } else {
        w.write_str(identifier)
    }
}

fn must_be_quoted(identifier: &str) -> bool {
    identifier.is_empty()
        || identifier.starts_with(|c: char| c.is_ascii_digit() || is_additional_identifier_char(c))
        || identifier.contains(is_delimiter_char)
        || identifier.contains("//")
        || identifier.contains("/*")
        || (identifier.contains(is_symbol_char)
            && identifier
                .contains(|c: char| !is_symbol_char(c) || is_additional_identifier_char(c)))
}

fn print_quoted(mut s: &str, quote: char, w: &mut impl fmt::Write) -> fmt::Result {
    w.write_char(quote)?;
    let mut iter = s.char_indices();
    while let Some((idx, mut c)) = iter.next() {
        match c {
            '\n' => c = 'n',
            '\r' => c = 'r',
            '\t' => c = 't',
            '\\' => (),
            _ => {
                if c != quote {
                    continue;
                }
            }
        }
        if idx > 0 {
            w.write_str(&s[..idx])?;
        }
        w.write_char('\\')?;
        w.write_char(c)?;
        s = iter.as_str();
        iter = s.char_indices();
    }
    if !s.is_empty() {
        w.write_str(s)?;
    }
    w.write_char(quote)?;
    Ok(())
}
