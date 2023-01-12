pub struct ParserInput<'a>(pub &'a str);

impl<'a> ParserInput<'a> {
    pub fn error<T>(&self, msg: String) -> Result<T, String> {
        Err(msg)
    }

    pub fn expected<T>(&self, expected: &str) -> Result<T, String> {
        let rest = self.0;
        self.error(format!("expected {expected} instead of: {rest}"))
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

    pub fn read_char(&mut self, c: char) -> Result<(), String> {
        self.skip_whitespace();
        if self.try_read_char(c) {
            Ok(())
        } else {
            self.expected(&format!("'{c}'"))
        }
    }

    pub fn try_read_name(&mut self) -> Option<&str> {
        let s = self.0;
        let end = s
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(s.len());
        if end == 0 {
            None
        } else {
            self.0 = &s[end..];
            Some(&s[..end])
        }
    }
}
