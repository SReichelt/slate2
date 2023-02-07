use anyhow::{anyhow, Error, Result};

pub struct ParserInput<'a>(pub &'a str);

impl<'a> ParserInput<'a> {
    pub fn error<T>(&self, err: Error) -> Result<T> {
        Err(err)
    }

    pub fn expected<T>(&self, expected: &str) -> Result<T> {
        let rest = self.0;
        self.error(anyhow!("expected {expected} instead of: {rest}"))
    }

    pub fn expect_end(&self) -> Result<()> {
        if self.0.is_empty() {
            Ok(())
        } else {
            self.expected("end")
        }
    }

    pub fn skip_whitespace(&mut self) {
        self.0 = self.0.trim_start();
    }

    pub fn try_read_char(&mut self, c: char) -> bool {
        if let Some(s) = self.0.strip_prefix(c) {
            self.0 = s;
            true
        } else {
            false
        }
    }

    pub fn read_char(&mut self, c: char) -> Result<()> {
        self.skip_whitespace();
        if self.try_read_char(c) {
            Ok(())
        } else {
            self.expected(&format!("'{c}'"))
        }
    }

    pub fn try_read_char_seq(&mut self, cs: &str) -> bool {
        if let Some(s) = self.0.strip_prefix(cs) {
            self.0 = s;
            true
        } else {
            false
        }
    }

    pub fn read_char_seq(&mut self, cs: &str) -> Result<()> {
        self.skip_whitespace();
        if self.try_read_char_seq(cs) {
            Ok(())
        } else {
            self.expected(&format!("'{cs}'"))
        }
    }

    fn is_name_char(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_' || c == '\''
    }

    pub fn try_read_name(&mut self) -> Option<&'a str> {
        let s = self.0;
        let end = s.find(|c: char| !Self::is_name_char(c)).unwrap_or(s.len());
        if end == 0 {
            None
        } else {
            self.0 = &s[end..];
            Some(&s[..end])
        }
    }
}
