// TODO: delete

use std::borrow::Cow;

use anyhow::{anyhow, Error, Result};

use crate::chars::*;

pub trait ParserInput<'a> {
    fn error<T>(&self, err: Error) -> Result<T> {
        Err(err)
    }

    fn expected<T>(&self, expected: &str) -> Result<T>;

    fn at_end(&self) -> bool;

    fn expect_end(&self) -> Result<()> {
        if self.at_end() {
            Ok(())
        } else {
            self.expected("end")
        }
    }

    fn skip_whitespace(&mut self);

    fn try_read_char(&mut self, c: char) -> bool;

    fn read_char(&mut self, c: char) -> Result<()> {
        self.skip_whitespace();
        if self.try_read_char(c) {
            Ok(())
        } else {
            self.expected(&format!("'{c}'"))
        }
    }

    fn try_read_char_seq(&mut self, cs: &str) -> bool;

    fn read_char_seq(&mut self, cs: &str) -> Result<()> {
        self.skip_whitespace();
        if self.try_read_char_seq(cs) {
            Ok(())
        } else {
            self.expected(&format!("'{cs}'"))
        }
    }

    // We support two different ways of dealing with identifiers.
    // * In languages where we want to reserve some characters for built-in syntax, we only allow
    //   ASCII alphanumeric characters plus underscore and apostrophe.
    // * In more flexible languages, identifiers can consist of almost arbitrary unicode characters;
    //   only whitespace and a few punctuation characters are reserved. The specific rules are
    //   described below. Additionally, any non-empty string can be an identifier when quoted.

    fn try_read_ascii_identifier(&mut self) -> Option<&'a str>;

    // Unquoted identifiers in flexible languages are handled as follows.
    // * An identifier may consist of either symbols or alphanumeric characters, but not both, so
    //   that expressions like `a+b` can be parsed as expected. The two types of characters can
    //   potentially span the entire unicode range, but we treat unknown characters as alphanumeric.
    //   Underscores and apostrophes are allowed in both cases.
    // * Whitespace, punctuation (in a narrow sense), and parentheses (including unicode) are not
    //   allowed to be part of identifiers, so that expressions like `f(x)` can be parsed.
    // * Other language rules may impose additional restrictions, such as that unquoted identifiers
    //   cannot start with an ASCII digit, an apostrophe, or a comment symbol. The printer takes
    //   these into account, but when parsing, these special cases should be checked before trying
    //   to read an identifier.

    fn try_read_identifier(&mut self) -> Result<Option<Cow<'a, str>>>;
}

pub struct StringInput<'a>(pub &'a str);

impl<'a> ParserInput<'a> for StringInput<'a> {
    fn expected<T>(&self, expected: &str) -> Result<T> {
        let rest = self.0;
        self.error(anyhow!("expected {expected} instead of: {rest}"))
    }

    fn at_end(&self) -> bool {
        self.0.is_empty()
    }

    fn skip_whitespace(&mut self) {
        self.0 = self.0.trim_start();
    }

    fn try_read_char(&mut self, c: char) -> bool {
        if let Some(s) = self.0.strip_prefix(c) {
            self.0 = s;
            true
        } else {
            false
        }
    }

    fn try_read_char_seq(&mut self, cs: &str) -> bool {
        if let Some(s) = self.0.strip_prefix(cs) {
            self.0 = s;
            true
        } else {
            false
        }
    }

    fn try_read_ascii_identifier(&mut self) -> Option<&'a str> {
        let s = self.0;
        let end = s
            .find(|c: char| !is_ascii_identifier_char(c))
            .unwrap_or_else(|| s.len());
        if end == 0 {
            None
        } else {
            self.0 = &s[end..];
            Some(&s[..end])
        }
    }

    fn try_read_identifier(&mut self) -> Result<Option<Cow<'a, str>>> {
        let s = self.0;
        if let Some(c) = s.chars().next() {
            if is_delimiter_char(c) {
                self.try_read_quoted('\"')
            } else if is_symbol_char(c) {
                let end = s
                    .find(|c: char| is_delimiter_char(c) || !is_symbol_char(c))
                    .unwrap_or_else(|| s.len());
                self.0 = &s[end..];
                Ok(Some(Cow::Borrowed(&s[..end])))
            } else {
                let end = s
                    .find(|c: char| {
                        is_delimiter_char(c)
                            || (is_symbol_char(c) && !is_additional_identifier_char(c))
                    })
                    .unwrap_or_else(|| s.len());
                self.0 = &s[end..];
                Ok(Some(Cow::Borrowed(&s[..end])))
            }
        } else {
            Ok(None)
        }
    }
}

impl<'a> StringInput<'a> {
    fn try_read_quoted(&mut self, quote: char) -> Result<Option<Cow<'a, str>>> {
        if self.try_read_char(quote) {
            let mut s = self.0;
            let mut result = String::new();
            let mut iter = s.char_indices();
            while let Some((idx, c)) = iter.next() {
                if c == quote {
                    self.0 = iter.as_str();
                    if result.is_empty() {
                        return Ok(Some(Cow::Borrowed(&s[..idx])));
                    } else {
                        result += &s[..idx];
                        return Ok(Some(Cow::Owned(result)));
                    }
                } else if c == '\\' {
                    result += &s[..idx];
                    if let Some((_, c)) = iter.next() {
                        match c {
                            'n' => result.push('\n'),
                            'r' => result.push('\r'),
                            't' => result.push('\t'),
                            '\\' | '\'' | '\"' => result.push(c),
                            _ => return self.error(anyhow!("unsupported escape character '{c}'")),
                        }
                    } else {
                        break;
                    }
                    s = iter.as_str();
                    iter = s.char_indices();
                }
            }
            self.error(anyhow!("unterminated string"))
        } else {
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ascii_identifier() {
        test_ascii_identifier("", None, "");
        test_ascii_identifier("!", None, "!");
        test_ascii_identifier("a", Some("a"), "");
        test_ascii_identifier("a!", Some("a"), "!");
        test_ascii_identifier("a ", Some("a"), " ");
        test_ascii_identifier("ab", Some("ab"), "");
        test_ascii_identifier("ab!", Some("ab"), "!");
        test_ascii_identifier("a'!", Some("a'"), "!");
        test_ascii_identifier("a_b", Some("a_b"), "");
    }

    fn test_ascii_identifier(s: &str, expected_identifier: Option<&str>, expected_rest: &str) {
        let mut input = StringInput(s);
        let identifier = input.try_read_ascii_identifier();
        assert_eq!(identifier, expected_identifier);
        assert_eq!(input.0, expected_rest);
    }

    #[test]
    fn general_identifier() -> Result<()> {
        test_general_identifier("", None, "")?;
        test_general_identifier(".", None, ".")?;
        test_general_identifier("a", Some("a"), "")?;
        test_general_identifier("!", Some("!"), "")?;
        test_general_identifier("a.", Some("a"), ".")?;
        test_general_identifier("a ", Some("a"), " ")?;
        test_general_identifier("a(b)", Some("a"), "(b)")?;
        test_general_identifier("a⟦b⟧", Some("a"), "⟦b⟧")?;
        test_general_identifier("!.", Some("!"), ".")?;
        test_general_identifier("!(?)", Some("!"), "(?)")?;
        test_general_identifier("!⟦?⟧", Some("!"), "⟦?⟧")?;
        test_general_identifier("a!", Some("a"), "!")?;
        test_general_identifier("!a", Some("!"), "a")?;
        test_general_identifier("ab", Some("ab"), "")?;
        test_general_identifier("!?", Some("!?"), "")?;
        test_general_identifier("ab!", Some("ab"), "!")?;
        test_general_identifier("!?a", Some("!?"), "a")?;
        test_general_identifier("a'!", Some("a'"), "!")?;
        test_general_identifier("!'a", Some("!'"), "a")?;
        test_general_identifier("a_b", Some("a_b"), "")?;
        test_general_identifier("\"\"", Some(""), "")?;
        test_general_identifier("\" \"", Some(" "), "")?;
        test_general_identifier("\" \" ", Some(" "), " ")?;
        test_general_identifier("\"a\"", Some("a"), "")?;
        test_general_identifier("\"a!\"", Some("a!"), "")?;
        test_general_identifier("\"a\\\"b\"", Some("a\"b"), "")?;
        test_general_identifier("\"a'\"", Some("a'"), "")?;
        test_general_identifier("\"a\\'\"", Some("a'"), "")?;
        test_general_identifier("\"a\\\\b\"", Some("a\\b"), "")?;
        test_general_identifier("\"a\\nb\"", Some("a\nb"), "")?;
        Ok(())
    }

    fn test_general_identifier(
        s: &str,
        expected_identifier: Option<&str>,
        expected_rest: &str,
    ) -> Result<()> {
        let mut input = StringInput(s);
        let identifier_cow = input.try_read_identifier()?;
        let identifier = if let Some(identifier_cow) = &identifier_cow {
            Some(identifier_cow.as_ref())
        } else {
            None
        };
        assert_eq!(identifier, expected_identifier);
        assert_eq!(input.0, expected_rest);
        Ok(())
    }
}
