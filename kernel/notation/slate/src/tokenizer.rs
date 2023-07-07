use std::{borrow::Cow, mem::take, ops::Range};

use slate_kernel_notation_generic::{event::*, event_translator::*};

use crate::chars::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Token<'a> {
    ReservedChar(char),
    DefinitionSymbol(Cow<'a, str>),
    Keyword(Cow<'a, str>),
    Number(Cow<'a, str>),
    SingleQuotedString(Cow<'a, str>),
    DoubleQuotedString(Cow<'a, str>),
    Identifier(Cow<'a, str>),
}

impl Event for Token<'_> {}

pub struct Tokenizer;

impl<'a> EventTranslator<'a> for Tokenizer {
    type In = char;
    type Out = Token<'a>;
    type Pass<Src: EventSource + 'a> = TokenizerPass<'a, Src>;

    fn start<Src: EventSource + 'a>(
        &self,
        source: Src,
        special_ops: <Self::In as Event>::SpecialOps<'a, Src::Marker>,
    ) -> Self::Pass<Src> {
        TokenizerPass {
            source,
            special_ops,
        }
    }
}

pub struct TokenizerPass<'a, Src: EventSource + 'a> {
    source: Src,
    special_ops: <char as Event>::SpecialOps<'a, Src::Marker>,
}

impl<'a, Src: EventSource + 'a> EventTranslatorPass for TokenizerPass<'a, Src> {
    type In = char;
    type Out = Token<'a>;
    type Marker = Src::Marker;
    type State = TokenizerState<Src::Marker>;

    fn new_state(&self) -> Self::State {
        None
    }

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        range: Range<&Self::Marker>,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) {
        if self.handle_char_in_current_state(state, event, &range, &mut out) {
            return;
        }

        assert!(state.is_none());

        let mut start_token = |token| {
            *state = Some(StartedTokenState {
                token_start: range.start.clone(),
                token,
            });
        };

        match event {
            ':' => {
                start_token(StartedToken::DefinitionSymbol);
            }
            '%' => {
                start_token(StartedToken::Keyword {
                    keyword_start: range.end.clone(),
                });
            }
            '@' => {
                start_token(StartedToken::String {
                    is_quoted_identifier: true,
                    is_double_quoted: false,
                    content_start: None,
                    escape_start: None,
                    value: None,
                });
            }
            '\'' | '"' => {
                start_token(StartedToken::String {
                    is_quoted_identifier: false,
                    is_double_quoted: event == '"',
                    content_start: Some(range.end.clone()),
                    escape_start: None,
                    value: None,
                });
            }
            c => {
                if is_delimiter_char(c) {
                    if !c.is_whitespace() {
                        out(Token::ReservedChar(c), range);
                    }
                } else if c.is_ascii_digit() {
                    start_token(StartedToken::Number {
                        number_state: NumberState::BeforeDot,
                    });
                } else {
                    start_token(StartedToken::UnquotedIdentifier {
                        is_symbol: if c == '_' {
                            None
                        } else {
                            Some(is_symbol_char(c))
                        },
                        is_slash: c == '/',
                    });
                }
            }
        }
    }

    fn next_pass(
        self,
        mut state: Self::State,
        end_marker: &Self::Marker,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        self.handle_char_in_current_state(&mut state, '\0', &(end_marker..end_marker), &mut out);

        if let Some(StartedTokenState { token_start, token }) = state {
            self.source.diagnostic(
                &token_start..end_marker,
                Severity::Error,
                match token {
                    StartedToken::BlockComment { .. } | StartedToken::LineComment => {
                        format!("unterminated comment")
                    }
                    StartedToken::String { .. } => format!("unterminated string"),
                    _ => format!("unterminated token"),
                },
            );
        }

        None
    }
}

impl<'a, Src: EventSource + 'a> TokenizerPass<'a, Src> {
    fn handle_char_in_current_state(
        &self,
        state: &mut TokenizerState<Src::Marker>,
        c: char,
        range: &Range<&Src::Marker>,
        out: &mut impl FnMut(Token<'a>, Range<&Src::Marker>),
    ) -> bool {
        let Some(StartedTokenState { token_start, token }) = state else {
            return false;
        };

        match token {
            StartedToken::LineComment => {
                if c == '\r' || c == '\n' || c == '\0' {
                    *state = None;
                    return false;
                }
            }

            StartedToken::BlockComment {
                nesting_level,
                slash_seen,
                asterisk_seen,
            } => {
                if *slash_seen {
                    *slash_seen = false;
                    if c == '*' {
                        *nesting_level += 1;
                        return true;
                    }
                } else if *asterisk_seen {
                    *asterisk_seen = false;
                    if c == '/' {
                        if *nesting_level > 0 {
                            *nesting_level -= 1;
                        } else {
                            *state = None;
                        }
                        return true;
                    }
                }
                if c == '/' {
                    *slash_seen = true;
                } else if c == '*' {
                    *asterisk_seen = true;
                }
            }

            StartedToken::DefinitionSymbol => {
                if !is_symbol_char(c) || (is_delimiter_char(c) && c != ':') {
                    let symbol = self.special_ops.slice(&*token_start..range.start);
                    out(Token::DefinitionSymbol(symbol), &*token_start..range.start);
                    *state = None;
                    return false;
                }
            }

            StartedToken::Keyword { keyword_start } => {
                if !is_keyword_char(c) {
                    if *keyword_start == *range.start {
                        self.source.diagnostic(
                            &*token_start..range.start,
                            Severity::Error,
                            format!("'%' must be followed by a keyword"),
                        );
                    } else {
                        let keyword = self.special_ops.slice(&*keyword_start..range.start);
                        out(Token::Keyword(keyword), &*token_start..range.start);
                    }
                    *state = None;
                    return false;
                }
            }

            StartedToken::Number { number_state } => {
                let is_alnum = c.is_ascii_alphanumeric() || c == '_';
                let is_special = match number_state {
                    NumberState::BeforeDot => {
                        if c == '.' {
                            *number_state = NumberState::AfterDot;
                            true
                        } else {
                            false
                        }
                    }
                    NumberState::AfterDot => {
                        if c == 'E' || c == 'e' {
                            *number_state = NumberState::BehindE;
                        }
                        false
                    }
                    NumberState::BehindE => {
                        *number_state = NumberState::InExponent;
                        c == '+' || c == '-'
                    }
                    NumberState::InExponent => false,
                };
                if !(is_alnum || is_special) {
                    let number = self.special_ops.slice(&*token_start..range.start);
                    out(Token::Number(number), &*token_start..range.start);
                    *state = None;
                    return false;
                }
            }

            StartedToken::String {
                is_quoted_identifier,
                is_double_quoted,
                content_start,
                escape_start,
                value,
            } => {
                if let Some(content_start) = content_start {
                    let mut end_string = || {
                        let final_value = if let Some(value) = value {
                            Cow::Owned(take(value))
                        } else {
                            self.special_ops.slice(&*content_start..range.start)
                        };
                        if *is_quoted_identifier {
                            Token::Identifier(final_value)
                        } else if *is_double_quoted {
                            Token::DoubleQuotedString(final_value)
                        } else {
                            Token::SingleQuotedString(final_value)
                        }
                    };

                    if c.is_ascii_control() && c != '\t' {
                        self.source.diagnostic(
                            &*token_start..range.start,
                            Severity::Error,
                            format!("unterminated string"),
                        );
                        let token = end_string();
                        out(token, &*token_start..range.start);
                        *state = None;
                        return false;
                    }

                    if let Some(some_escape_start) = escape_start {
                        let escape_prefix =
                            self.special_ops.slice(&*some_escape_start..range.start);
                        if escape_prefix == "\\" {
                            if let Some(c) = match c {
                                'x' | 'u' => None,
                                '0' => Some('\0'),
                                'n' => Some('\n'),
                                'r' => Some('\r'),
                                't' => Some('\t'),
                                '\\' | '\'' | '"' => Some(c),
                                _ => {
                                    self.source.diagnostic(
                                        &*some_escape_start..range.end,
                                        Severity::Error,
                                        format!("invalid escape sequence"),
                                    );
                                    Some(c)
                                }
                            } {
                                value.as_mut().unwrap().push(c);
                                *escape_start = None;
                            }
                            return true;
                        } else if let Some(ascii) = escape_prefix.strip_prefix("\\x") {
                            if c.is_ascii_hexdigit() {
                                if !ascii.is_empty() {
                                    let ascii = format!("{ascii}{c}");
                                    let code = u8::from_str_radix(&ascii, 16).unwrap();
                                    value.as_mut().unwrap().push(code as char);
                                    *escape_start = None;
                                }
                                return true;
                            } else {
                                self.source.diagnostic(
                                    &*some_escape_start..range.start,
                                    Severity::Error,
                                    format!("'\\x' must be followed by two hexadecimal digits"),
                                );
                                *escape_start = None;
                            }
                        } else if let Some(unicode) = escape_prefix.strip_prefix("\\u") {
                            if let Some(unicode) = unicode.strip_prefix('{') {
                                if c == '}' {
                                    if let Ok(code) = u32::from_str_radix(unicode, 16) {
                                        if let Some(c) = char::from_u32(code) {
                                            value.as_mut().unwrap().push(c);
                                            *escape_start = None;
                                            return true;
                                        }
                                    }
                                    self.source.diagnostic(
                                        &*some_escape_start..range.end,
                                        Severity::Error,
                                        format!(
                                            "'{unicode}' is not a valid Unicode character code"
                                        ),
                                    );
                                    *escape_start = None;
                                    return true;
                                } else if c.is_ascii_hexdigit() {
                                    return true;
                                } else {
                                    self.source.diagnostic(
                                        &*some_escape_start..range.start,
                                        Severity::Error,
                                        format!("'\\u' must be followed by a hexadecimal number in braces"),
                                    );
                                    *escape_start = None;
                                }
                            } else if c == '{' {
                                return true;
                            } else {
                                self.source.diagnostic(
                                    &*some_escape_start..range.start,
                                    Severity::Error,
                                    format!(
                                        "'\\u' must be followed by a hexadecimal number in braces"
                                    ),
                                );
                                *escape_start = None;
                            }
                        } else {
                            panic!("inconsistent escape sequence state");
                        }
                    }

                    let quote_char = if *is_double_quoted { '"' } else { '\'' };
                    if c == quote_char {
                        let token = end_string();
                        out(token, &*token_start..range.end);
                        *state = None;
                    } else if c == '\\' {
                        *escape_start = Some(range.start.clone());
                        if value.is_none() {
                            *value = Some(
                                self.special_ops
                                    .slice(&*content_start..range.start)
                                    .into_owned(),
                            );
                        }
                    } else {
                        if let Some(value) = value {
                            value.push(c);
                        }
                    }
                } else {
                    debug_assert!(*is_quoted_identifier);
                    if c == '\'' || c == '"' {
                        if c == '"' {
                            *is_double_quoted = true;
                        } else {
                            self.source.diagnostic(
                                &*token_start..range.start,
                                Severity::Error,
                                format!("'@' must be followed by double quotes"),
                            );
                        }
                        *content_start = Some(range.end.clone());
                    } else {
                        self.source.diagnostic(
                            &*token_start..range.start,
                            Severity::Error,
                            format!("'@' must be followed by a string"),
                        );
                        *state = None;
                        return false;
                    }
                }
            }

            StartedToken::UnquotedIdentifier {
                is_symbol,
                is_slash,
            } => {
                let mut end = is_delimiter_char(c);
                if !end {
                    if is_group_connecting_char(c) {
                        *is_symbol = None;
                    } else {
                        let c_is_symbol = is_symbol_char(c);
                        if let Some(is_symbol) = *is_symbol {
                            if c_is_symbol != is_symbol {
                                end = true;
                            }
                        } else {
                            *is_symbol = Some(c_is_symbol);
                        }
                    }
                }
                if end {
                    let identifier = self.special_ops.slice(&*token_start..range.start);
                    out(Token::Identifier(identifier), &*token_start..range.start);
                    *state = None;
                    return false;
                } else if *is_slash {
                    if c == '/' {
                        *token = StartedToken::LineComment;
                    } else if c == '*' {
                        *token = StartedToken::BlockComment {
                            nesting_level: 0,
                            slash_seen: false,
                            asterisk_seen: false,
                        };
                    } else {
                        *is_slash = false;
                    }
                }
            }
        }

        true
    }
}

pub type TokenizerState<Marker> = Option<StartedTokenState<Marker>>;

#[derive(Clone, PartialEq)]
pub struct StartedTokenState<Marker: Clone + PartialEq> {
    token_start: Marker,
    token: StartedToken<Marker>,
}

#[derive(Clone, PartialEq)]
enum StartedToken<Marker: Clone + PartialEq> {
    LineComment,
    BlockComment {
        nesting_level: u32,
        slash_seen: bool,
        asterisk_seen: bool,
    },
    DefinitionSymbol,
    Keyword {
        keyword_start: Marker,
    },
    Number {
        number_state: NumberState,
    },
    String {
        is_quoted_identifier: bool,
        is_double_quoted: bool,
        content_start: Option<Marker>,
        escape_start: Option<Marker>,
        value: Option<String>,
    },
    UnquotedIdentifier {
        is_symbol: Option<bool>,
        is_slash: bool,
    },
}

#[derive(Clone, PartialEq)]
enum NumberState {
    BeforeDot,
    AfterDot,
    BehindE,
    InExponent,
}

#[cfg(test)]
mod tests {
    use slate_kernel_notation_generic::char_slice::{test_helpers::*, *};

    use super::*;

    #[test]
    fn whitespace() -> Result<(), Message> {
        test_tokenization("", &[], &[])?;
        test_tokenization(" ", &[], &[])?;
        test_tokenization("\t", &[], &[])?;
        test_tokenization(" \n\t\r\n ", &[], &[])?;
        test_tokenization("/**/", &[], &[])?;
        test_tokenization("/* */", &[], &[])?;
        test_tokenization(
            " /* abc \n def */ . /* ghi */ ",
            &[Token::ReservedChar('.')],
            &[],
        )?;
        test_tokenization("/***/", &[], &[])?;
        test_tokenization("/*/**/*/", &[], &[])?;
        test_tokenization("/**/*/", &[Token::Identifier("*/".into())], &[])?;
        test_tokenization("/* // */", &[], &[])?;
        test_tokenization(
            "/*",
            &[],
            &[TestDiagnosticMessage {
                range_text: "/*".into(),
                severity: Severity::Error,
                msg: "unterminated comment".into(),
            }],
        )?;
        test_tokenization(
            " /*/ ",
            &[],
            &[TestDiagnosticMessage {
                range_text: "/*/ ".into(),
                severity: Severity::Error,
                msg: "unterminated comment".into(),
            }],
        )?;
        test_tokenization(
            "/*/**/",
            &[],
            &[TestDiagnosticMessage {
                range_text: "/*/**/".into(),
                severity: Severity::Error,
                msg: "unterminated comment".into(),
            }],
        )?;
        test_tokenization(
            "/*//*/",
            &[],
            &[TestDiagnosticMessage {
                range_text: "/*//*/".into(),
                severity: Severity::Error,
                msg: "unterminated comment".into(),
            }],
        )?;
        test_tokenization("//", &[], &[])?;
        test_tokenization("///", &[], &[])?;
        test_tokenization("//\n", &[], &[])?;
        test_tokenization("//\n.", &[Token::ReservedChar('.')], &[])?;
        test_tokenization(
            " . // : \n .",
            &[Token::ReservedChar('.'), Token::ReservedChar('.')],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn reserved_chars() -> Result<(), Message> {
        test_tokenization(".", &[Token::ReservedChar('.')], &[])?;
        test_tokenization(" . ", &[Token::ReservedChar('.')], &[])?;
        test_tokenization(
            "..",
            &[Token::ReservedChar('.'), Token::ReservedChar('.')],
            &[],
        )?;
        test_tokenization(
            " . . ",
            &[Token::ReservedChar('.'), Token::ReservedChar('.')],
            &[],
        )?;
        test_tokenization(
            ".,;()[]{}|〈〉",
            &[
                Token::ReservedChar('.'),
                Token::ReservedChar(','),
                Token::ReservedChar(';'),
                Token::ReservedChar('('),
                Token::ReservedChar(')'),
                Token::ReservedChar('['),
                Token::ReservedChar(']'),
                Token::ReservedChar('{'),
                Token::ReservedChar('}'),
                Token::ReservedChar('|'),
                Token::ReservedChar('〈'),
                Token::ReservedChar('〉'),
            ],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn definition_symbols() -> Result<(), Message> {
        test_tokenization(":", &[Token::DefinitionSymbol(":".into())], &[])?;
        test_tokenization(" : ", &[Token::DefinitionSymbol(":".into())], &[])?;
        test_tokenization(":=", &[Token::DefinitionSymbol(":=".into())], &[])?;
        test_tokenization(":=:", &[Token::DefinitionSymbol(":=:".into())], &[])?;
        test_tokenization(
            "a:=b",
            &[
                Token::Identifier("a".into()),
                Token::DefinitionSymbol(":=".into()),
                Token::Identifier("b".into()),
            ],
            &[],
        )?;
        test_tokenization(
            " : : ",
            &[
                Token::DefinitionSymbol(":".into()),
                Token::DefinitionSymbol(":".into()),
            ],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn keywords() -> Result<(), Message> {
        test_tokenization("%x", &[Token::Keyword("x".into())], &[])?;
        test_tokenization("%for", &[Token::Keyword("for".into())], &[])?;
        test_tokenization("%for_each", &[Token::Keyword("for_each".into())], &[])?;
        test_tokenization(" %for ", &[Token::Keyword("for".into())], &[])?;
        test_tokenization(
            "%for %each",
            &[Token::Keyword("for".into()), Token::Keyword("each".into())],
            &[],
        )?;
        test_tokenization(
            "%for.each",
            &[
                Token::Keyword("for".into()),
                Token::ReservedChar('.'),
                Token::Identifier("each".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "%for'each'",
            &[
                Token::Keyword("for".into()),
                Token::SingleQuotedString("each".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "%",
            &[],
            &[TestDiagnosticMessage {
                range_text: "%".into(),
                severity: Severity::Error,
                msg: "'%' must be followed by a keyword".into(),
            }],
        )?;
        test_tokenization(
            "% x",
            &[Token::Identifier("x".into())],
            &[TestDiagnosticMessage {
                range_text: "%".into(),
                severity: Severity::Error,
                msg: "'%' must be followed by a keyword".into(),
            }],
        )?;
        test_tokenization(
            "%+",
            &[Token::Identifier("+".into())],
            &[TestDiagnosticMessage {
                range_text: "%".into(),
                severity: Severity::Error,
                msg: "'%' must be followed by a keyword".into(),
            }],
        )?;
        test_tokenization(
            "%%",
            &[],
            &[
                TestDiagnosticMessage {
                    range_text: "%".into(),
                    severity: Severity::Error,
                    msg: "'%' must be followed by a keyword".into(),
                },
                TestDiagnosticMessage {
                    range_text: "%".into(),
                    severity: Severity::Error,
                    msg: "'%' must be followed by a keyword".into(),
                },
            ],
        )?;
        Ok(())
    }

    #[test]
    fn identifiers() -> Result<(), Message> {
        test_tokenization("x", &[Token::Identifier("x".into())], &[])?;
        test_tokenization("+", &[Token::Identifier("+".into())], &[])?;
        test_tokenization("xyz", &[Token::Identifier("xyz".into())], &[])?;
        test_tokenization("+-", &[Token::Identifier("+-".into())], &[])?;
        test_tokenization("a1", &[Token::Identifier("a1".into())], &[])?;
        test_tokenization("a'", &[Token::Identifier("a'".into())], &[])?;
        test_tokenization("a\"", &[Token::Identifier("a\"".into())], &[])?;
        test_tokenization("a''", &[Token::Identifier("a''".into())], &[])?;
        test_tokenization("a'b", &[Token::Identifier("a'b".into())], &[])?;
        test_tokenization("a'+", &[Token::Identifier("a'+".into())], &[])?;
        test_tokenization("a_1", &[Token::Identifier("a_1".into())], &[])?;
        test_tokenization("a_+", &[Token::Identifier("a_+".into())], &[])?;
        test_tokenization("+_a", &[Token::Identifier("+_a".into())], &[])?;
        test_tokenization("a_+_b", &[Token::Identifier("a_+_b".into())], &[])?;
        test_tokenization("+_ab_*", &[Token::Identifier("+_ab_*".into())], &[])?;
        test_tokenization("_a", &[Token::Identifier("_a".into())], &[])?;
        test_tokenization("_+", &[Token::Identifier("_+".into())], &[])?;
        test_tokenization(
            "x y z",
            &[
                Token::Identifier("x".into()),
                Token::Identifier("y".into()),
                Token::Identifier("z".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "x + y",
            &[
                Token::Identifier("x".into()),
                Token::Identifier("+".into()),
                Token::Identifier("y".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "x+y",
            &[
                Token::Identifier("x".into()),
                Token::Identifier("+".into()),
                Token::Identifier("y".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "x_+y",
            &[
                Token::Identifier("x_+".into()),
                Token::Identifier("y".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "xy+=z",
            &[
                Token::Identifier("xy".into()),
                Token::Identifier("+=".into()),
                Token::Identifier("z".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "x' *' y\"",
            &[
                Token::Identifier("x'".into()),
                Token::Identifier("*'".into()),
                Token::Identifier("y\"".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "x '*' y\"",
            &[
                Token::Identifier("x".into()),
                Token::SingleQuotedString("*".into()),
                Token::Identifier("y\"".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "x.y",
            &[
                Token::Identifier("x".into()),
                Token::ReservedChar('.'),
                Token::Identifier("y".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "-.-",
            &[
                Token::Identifier("-".into()),
                Token::ReservedChar('.'),
                Token::Identifier("-".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "f(x)",
            &[
                Token::Identifier("f".into()),
                Token::ReservedChar('('),
                Token::Identifier("x".into()),
                Token::ReservedChar(')'),
            ],
            &[],
        )?;
        test_tokenization(
            "f(-)",
            &[
                Token::Identifier("f".into()),
                Token::ReservedChar('('),
                Token::Identifier("-".into()),
                Token::ReservedChar(')'),
            ],
            &[],
        )?;
        test_tokenization(
            "f(xy,-)",
            &[
                Token::Identifier("f".into()),
                Token::ReservedChar('('),
                Token::Identifier("xy".into()),
                Token::ReservedChar(','),
                Token::Identifier("-".into()),
                Token::ReservedChar(')'),
            ],
            &[],
        )?;
        test_tokenization(
            "x @\".\" y",
            &[
                Token::Identifier("x".into()),
                Token::Identifier(".".into()),
                Token::Identifier("y".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "x@\".\"y",
            &[
                Token::Identifier("x".into()),
                Token::Identifier(".".into()),
                Token::Identifier("y".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "x@y",
            &[Token::Identifier("x".into()), Token::Identifier("y".into())],
            &[TestDiagnosticMessage {
                range_text: "@".into(),
                severity: Severity::Error,
                msg: "'@' must be followed by a string".into(),
            }],
        )?;
        test_tokenization(
            "x@'.'y",
            &[
                Token::Identifier("x".into()),
                Token::Identifier(".".into()),
                Token::Identifier("y".into()),
            ],
            &[TestDiagnosticMessage {
                range_text: "@".into(),
                severity: Severity::Error,
                msg: "'@' must be followed by double quotes".into(),
            }],
        )?;
        test_tokenization("@\"x+y.z\"", &[Token::Identifier("x+y.z".into())], &[])?;
        test_tokenization("@\"\"", &[Token::Identifier("".into())], &[])?;
        test_tokenization("@\"\\n\"", &[Token::Identifier("\n".into())], &[])?;
        test_tokenization(
            "abc @\"def",
            &[
                Token::Identifier("abc".into()),
                Token::Identifier("def".into()),
            ],
            &[TestDiagnosticMessage {
                range_text: "@\"def".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
        )?;
        Ok(())
    }

    #[test]
    fn numbers() -> Result<(), Message> {
        test_tokenization("0", &[Token::Number("0".into())], &[])?;
        test_tokenization("123", &[Token::Number("123".into())], &[])?;
        test_tokenization("12.345", &[Token::Number("12.345".into())], &[])?;
        test_tokenization("1_234_567.89", &[Token::Number("1_234_567.89".into())], &[])?;
        test_tokenization("12.34e5", &[Token::Number("12.34e5".into())], &[])?;
        test_tokenization("12.34e+56", &[Token::Number("12.34e+56".into())], &[])?;
        test_tokenization("12.3e-456", &[Token::Number("12.3e-456".into())], &[])?;
        test_tokenization("0xf00", &[Token::Number("0xf00".into())], &[])?;
        test_tokenization(
            " 0 1 .2 3 ",
            &[
                Token::Number("0".into()),
                Token::Number("1".into()),
                Token::ReservedChar('.'),
                Token::Number("2".into()),
                Token::Number("3".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "1+2.3e4-5",
            &[
                Token::Number("1".into()),
                Token::Identifier("+".into()),
                Token::Number("2.3e4".into()),
                Token::Identifier("-".into()),
                Token::Number("5".into()),
            ],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn strings() -> Result<(), Message> {
        test_tokenization("''", &[Token::SingleQuotedString("".into())], &[])?;
        test_tokenization("'abc'", &[Token::SingleQuotedString("abc".into())], &[])?;
        test_tokenization("'\"'", &[Token::SingleQuotedString("\"".into())], &[])?;
        test_tokenization("'/*'", &[Token::SingleQuotedString("/*".into())], &[])?;
        test_tokenization("\"\"", &[Token::DoubleQuotedString("".into())], &[])?;
        test_tokenization("\"abc\"", &[Token::DoubleQuotedString("abc".into())], &[])?;
        test_tokenization("\"'\"", &[Token::DoubleQuotedString("'".into())], &[])?;
        test_tokenization("\"/*\"", &[Token::DoubleQuotedString("/*".into())], &[])?;
        test_tokenization(
            "'abc'\"abc\"",
            &[
                Token::SingleQuotedString("abc".into()),
                Token::DoubleQuotedString("abc".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "\"abc\"\"abc\"",
            &[
                Token::DoubleQuotedString("abc".into()),
                Token::DoubleQuotedString("abc".into()),
            ],
            &[],
        )?;
        test_tokenization(
            " 'abc' \"abc\" ",
            &[
                Token::SingleQuotedString("abc".into()),
                Token::DoubleQuotedString("abc".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "\"abc /*def*/ ghi\"",
            &[Token::DoubleQuotedString("abc /*def*/ ghi".into())],
            &[],
        )?;
        test_tokenization("'\\n'", &[Token::SingleQuotedString("\n".into())], &[])?;
        test_tokenization("'\\\''", &[Token::SingleQuotedString("'".into())], &[])?;
        test_tokenization("'\\\\'", &[Token::SingleQuotedString("\\".into())], &[])?;
        test_tokenization("\"\\n\"", &[Token::DoubleQuotedString("\n".into())], &[])?;
        test_tokenization("\"\\\"\"", &[Token::DoubleQuotedString("\"".into())], &[])?;
        test_tokenization("\"\\\\\"", &[Token::DoubleQuotedString("\\".into())], &[])?;
        test_tokenization(
            "\"abc\\ndef\"",
            &[Token::DoubleQuotedString("abc\ndef".into())],
            &[],
        )?;
        test_tokenization(
            "\"abc\\r\\n\\tdef\\0\"",
            &[Token::DoubleQuotedString("abc\r\n\tdef\0".into())],
            &[],
        )?;
        test_tokenization(
            "\"\\x17\"",
            &[Token::DoubleQuotedString("\x17".into())],
            &[],
        )?;
        test_tokenization(
            "\"\\x0c\"",
            &[Token::DoubleQuotedString("\x0c".into())],
            &[],
        )?;
        test_tokenization(
            "\"abc\\x17def\"",
            &[Token::DoubleQuotedString("abc\x17def".into())],
            &[],
        )?;
        test_tokenization(
            "\"\\u{17}\"",
            &[Token::DoubleQuotedString("\u{17}".into())],
            &[],
        )?;
        test_tokenization(
            "\"abc\\u{17}def\"",
            &[Token::DoubleQuotedString("abc\u{17}def".into())],
            &[],
        )?;
        test_tokenization(
            "\"\\u42\"",
            &[Token::DoubleQuotedString("42".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u".into(),
                severity: Severity::Error,
                msg: "'\\u' must be followed by a hexadecimal number in braces".into(),
            }],
        )?;
        test_tokenization(
            "\"\\u{}\"",
            &[Token::DoubleQuotedString("".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u{}".into(),
                severity: Severity::Error,
                msg: "'' is not a valid Unicode character code".into(),
            }],
        )?;
        test_tokenization(
            "\"\\u{e3a}\"",
            &[Token::DoubleQuotedString("\u{e3a}".into())],
            &[],
        )?;
        test_tokenization(
            "\"\\u{e3g}\"",
            &[Token::DoubleQuotedString("g}".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u{e3".into(),
                severity: Severity::Error,
                msg: "'\\u' must be followed by a hexadecimal number in braces".into(),
            }],
        )?;
        test_tokenization(
            "\"\\u{d800}\"",
            &[Token::DoubleQuotedString("".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u{d800}".into(),
                severity: Severity::Error,
                msg: "'d800' is not a valid Unicode character code".into(),
            }],
        )?;
        test_tokenization(
            "\"\\u{10000}\"",
            &[Token::DoubleQuotedString("\u{10000}".into())],
            &[],
        )?;
        test_tokenization(
            "\"abc\\u{10000000}def\"",
            &[Token::DoubleQuotedString("abcdef".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u{10000000}".into(),
                severity: Severity::Error,
                msg: "'10000000' is not a valid Unicode character code".into(),
            }],
        )?;
        test_tokenization(
            "\"a\\bc\"",
            &[Token::DoubleQuotedString("abc".into())],
            &[TestDiagnosticMessage {
                range_text: "\\b".into(),
                severity: Severity::Error,
                msg: "invalid escape sequence".into(),
            }],
        )?;
        test_tokenization(
            "\"",
            &[Token::DoubleQuotedString("".into())],
            &[TestDiagnosticMessage {
                range_text: "\"".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
        )?;
        test_tokenization(
            " abc \" def ",
            &[
                Token::Identifier("abc".into()),
                Token::DoubleQuotedString(" def ".into()),
            ],
            &[TestDiagnosticMessage {
                range_text: "\" def ".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
        )?;
        test_tokenization(
            " abc \" def \\",
            &[
                Token::Identifier("abc".into()),
                Token::DoubleQuotedString(" def ".into()),
            ],
            &[TestDiagnosticMessage {
                range_text: "\" def \\".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
        )?;
        test_tokenization(
            "abc \"def\nghi",
            &[
                Token::Identifier("abc".into()),
                Token::DoubleQuotedString("def".into()),
                Token::Identifier("ghi".into()),
            ],
            &[TestDiagnosticMessage {
                range_text: "\"def".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
        )?;
        test_tokenization(
            "abc \"def\\\nghi",
            &[
                Token::Identifier("abc".into()),
                Token::DoubleQuotedString("def".into()),
                Token::Identifier("ghi".into()),
            ],
            &[TestDiagnosticMessage {
                range_text: "\"def\\".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
        )?;
        Ok(())
    }

    fn test_tokenization(
        input: &str,
        expected_tokens: &[Token],
        expected_diagnostics: &[TestDiagnosticMessage],
    ) -> Result<(), Message> {
        let mut tokens = Vec::new();
        let char_sink = TranslatorInst::new(Tokenizer, &mut tokens);
        let diag_sink = DiagnosticsRecorder::new(input);
        let source = CharSliceEventSource::new(input, &diag_sink)?;
        source.run(char_sink);
        assert_eq!(tokens, expected_tokens);
        assert_eq!(diag_sink.diagnostics(), expected_diagnostics);
        Ok(())
    }
}
