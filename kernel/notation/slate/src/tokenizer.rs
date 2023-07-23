use std::{borrow::Cow, mem::take, ops::Range};

use slate_kernel_notation_generic::{char::*, event::*, event_translator::*};

use crate::chars::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Token<'a> {
    ReservedChar(char, TokenIsolation, TokenIsolation),
    Keyword(Cow<'a, str>),
    Number(Cow<'a, str>),
    SingleQuotedString(Cow<'a, str>),
    DoubleQuotedString(Cow<'a, str>),
    Identifier(Cow<'a, str>, IdentifierType),
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum TokenIsolation {
    Isolated,          // preceded/followed by whitespace
    WeaklyConnected,   // preceded/followed by punctuation or similar
    StronglyConnected, // preceded/followed by identifier or similar
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum IdentifierType {
    Unquoted,
    Quoted,
}

impl Event for Token<'_> {}

pub struct Tokenizer;

impl<'a> EventTranslator<'a> for Tokenizer {
    type In = char;
    type Out = Token<'a>;
    type Pass<Src: EventSource + 'a> = TokenizerPass<'a, Src>;

    fn start<Src: EventSource + 'a>(
        &self,
        source: EventSourceWithOps<'a, Self::In, Src>,
    ) -> Self::Pass<Src> {
        TokenizerPass { source }
    }
}

pub struct TokenizerPass<'a, Src: EventSource + 'a> {
    source: EventSourceWithOps<'a, char, Src>,
}

impl<'a, Src: EventSource + 'a> EventTranslatorPass for TokenizerPass<'a, Src> {
    type In = char;
    type Out = Token<'a>;
    type Marker = Src::Marker;
    type State = TokenizerState<Src::Marker>;

    fn new_state(&self) -> Self::State {
        TokenizerState {
            prev: '\0',
            after_dot: Some(false),
            dot_number_allowed: true,
            started_token: None,
        }
    }

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        range: Range<&Self::Marker>,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) {
        if !self.handle_char_in_current_state(state, event, &range, &mut out) {
            assert!(state.started_token.is_none());

            let mut start_token = |token| {
                state.started_token = Some(StartedTokenState {
                    token_start: range.start.clone(),
                    token,
                });
            };

            match event {
                '@' => start_token(StartedToken::String {
                    is_quoted_identifier: true,
                    is_double_quoted: false,
                    content_start: None,
                    escape_start: None,
                    value: None,
                }),
                '\'' | '"' => start_token(StartedToken::String {
                    is_quoted_identifier: false,
                    is_double_quoted: event == '"',
                    content_start: Some(range.end.clone()),
                    escape_start: None,
                    value: None,
                }),
                c if is_delimiter_char(c) => {
                    if !c.is_whitespace() {
                        let prev = state.prev;
                        let pre_isolation = if prev == '\0' || prev.is_whitespace() {
                            TokenIsolation::Isolated
                        } else if is_pre_weakly_connecting_char(prev) {
                            TokenIsolation::WeaklyConnected
                        } else {
                            TokenIsolation::StronglyConnected
                        };
                        start_token(StartedToken::ReservedChar { pre_isolation });
                    }
                }
                c if c.is_ascii_digit() && state.after_dot != Some(true) => {
                    start_token(StartedToken::Number {
                        number_state: NumberState::BeforeDot,
                    })
                }
                c => start_token(StartedToken::UnquotedIdentifier {
                    content: if c == '%' {
                        IdentifierContent::None
                    } else {
                        Self::identifier_content(c)
                    },
                }),
            }
        }

        state.prev = event;
    }

    fn next_pass(
        self,
        mut state: Self::State,
        end_marker: &Self::Marker,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        self.handle_char_in_current_state(&mut state, '\0', &(end_marker..end_marker), &mut out);

        if let Some(StartedTokenState { token_start, token }) = state.started_token {
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
        let Some(StartedTokenState { token_start, token }) = &mut state.started_token else {
            return false;
        };

        match token {
            StartedToken::LineComment => {
                if c == '\r' || c == '\n' || c == '\0' {
                    state.started_token = None;
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
                            state.started_token = None;
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

            StartedToken::Number { number_state } => {
                let is_alnum = c.is_ascii_alphanumeric() || c == '_';
                let is_special = match number_state {
                    NumberState::BeforeDot => {
                        if c == '.' {
                            *number_state = NumberState::AfterDot(Some(range.start.clone()));
                            true
                        } else {
                            false
                        }
                    }
                    NumberState::AfterDot(marker) => {
                        if c == '.' {
                            if let Some(marker) = marker {
                                let number = self.source.slice(&*token_start..&*marker);
                                out(Token::Number(number), &*token_start..&*marker);
                                out(
                                    Token::ReservedChar(
                                        '.',
                                        TokenIsolation::StronglyConnected,
                                        TokenIsolation::WeaklyConnected,
                                    ),
                                    &*marker..range.start,
                                );
                                *state = TokenizerState {
                                    prev: state.prev,
                                    after_dot: Some(true),
                                    dot_number_allowed: false,
                                    started_token: None,
                                };
                                return false;
                            }
                        }
                        *marker = None;
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
                    let number = self.source.slice(&*token_start..range.start);
                    out(Token::Number(number), &*token_start..range.start);
                    *state = TokenizerState {
                        prev: state.prev,
                        after_dot: Some(false),
                        dot_number_allowed: c != '.',
                        started_token: None,
                    };
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
                            self.source.slice(&*content_start..range.start)
                        };
                        if *is_quoted_identifier {
                            Token::Identifier(final_value, IdentifierType::Quoted)
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
                        *state = TokenizerState {
                            prev: state.prev,
                            after_dot: Some(false),
                            dot_number_allowed: false,
                            started_token: None,
                        };
                        return false;
                    }

                    if let Some(some_escape_start) = escape_start {
                        let escape_prefix = self.source.slice(&*some_escape_start..range.start);
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
                        *state = TokenizerState {
                            prev: state.prev,
                            after_dot: Some(false),
                            dot_number_allowed: false,
                            started_token: None,
                        };
                    } else if c == '\\' {
                        *escape_start = Some(range.start.clone());
                        if value.is_none() {
                            *value =
                                Some(self.source.slice(&*content_start..range.start).into_owned());
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
                        *state = TokenizerState {
                            prev: state.prev,
                            after_dot: Some(false),
                            dot_number_allowed: false,
                            started_token: None,
                        };
                        return false;
                    }
                }
            }

            StartedToken::UnquotedIdentifier { content } => {
                let mut end = is_delimiter_char(c);
                if !end {
                    if !is_prime_char(c) {
                        if is_prime_char(state.prev) {
                            end = true;
                        } else {
                            let c_content = Self::identifier_content(c);
                            if *content == IdentifierContent::None {
                                *content = c_content;
                            } else if c_content != *content {
                                end = true;
                            }
                        }
                    }
                }
                if end {
                    let identifier = self.source.slice(&*token_start..range.start);
                    let token = if identifier.starts_with('%') {
                        Token::Keyword(identifier)
                    } else {
                        Token::Identifier(identifier, IdentifierType::Unquoted)
                    };
                    out(token, &*token_start..range.start);
                    *state = TokenizerState {
                        prev: state.prev,
                        after_dot: Some(false),
                        dot_number_allowed: *content == IdentifierContent::Symbol,
                        started_token: None,
                    };
                    return false;
                } else if state.prev == '/' {
                    if c == '/' {
                        *token = StartedToken::LineComment;
                    } else if c == '*' {
                        *token = StartedToken::BlockComment {
                            nesting_level: 0,
                            slash_seen: false,
                            asterisk_seen: false,
                        };
                    }
                }
            }

            StartedToken::ReservedChar { pre_isolation } => {
                let ch = state.prev;
                if ch == '.' && state.dot_number_allowed && c.is_ascii_digit() {
                    *token = StartedToken::Number {
                        number_state: NumberState::AfterDot(Some(range.start.clone())),
                    };
                } else {
                    let post_isolation = if c == '\0' || c.is_whitespace() {
                        TokenIsolation::Isolated
                    } else if is_post_weakly_connecting_char(c) {
                        TokenIsolation::WeaklyConnected
                    } else {
                        TokenIsolation::StronglyConnected
                    };
                    out(
                        Token::ReservedChar(ch, *pre_isolation, post_isolation),
                        &*token_start..range.start,
                    );
                    *state = TokenizerState {
                        prev: ch,
                        after_dot: if ch == '.' {
                            if state.after_dot == Some(false) {
                                Some(true)
                            } else {
                                None
                            }
                        } else {
                            Some(false)
                        },
                        dot_number_allowed: ch == ',' || ch == ';' || is_opening_parenthesis(ch),
                        started_token: None,
                    };
                    return false;
                }
            }
        }

        true
    }

    fn identifier_content(c: char) -> IdentifierContent {
        if is_symbol_char(c) {
            IdentifierContent::Symbol
        } else if is_subscript_char(c) {
            IdentifierContent::Subscript
        } else if is_superscript_char(c) {
            IdentifierContent::Superscript
        } else {
            IdentifierContent::Alphanumeric
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct TokenizerState<Marker: Clone + PartialEq> {
    prev: char,
    after_dot: Option<bool>,
    dot_number_allowed: bool,
    started_token: Option<StartedTokenState<Marker>>,
}

#[derive(Clone, PartialEq)]
struct StartedTokenState<Marker: Clone + PartialEq> {
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
    Number {
        number_state: NumberState<Marker>,
    },
    String {
        is_quoted_identifier: bool,
        is_double_quoted: bool,
        content_start: Option<Marker>,
        escape_start: Option<Marker>,
        value: Option<String>,
    },
    UnquotedIdentifier {
        content: IdentifierContent,
    },
    ReservedChar {
        pre_isolation: TokenIsolation,
    },
}

#[derive(Clone, PartialEq)]
enum NumberState<Marker: Clone + PartialEq> {
    BeforeDot,
    AfterDot(Option<Marker>),
    BehindE,
    InExponent,
}

#[derive(Clone, PartialEq)]
enum IdentifierContent {
    None,
    Alphanumeric,
    Symbol,
    Subscript,
    Superscript,
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
            &[Token::ReservedChar(
                '.',
                TokenIsolation::Isolated,
                TokenIsolation::Isolated,
            )],
            &[],
        )?;
        test_tokenization("/***/", &[], &[])?;
        test_tokenization("/*/**/*/", &[], &[])?;
        test_tokenization(
            "/**/*/",
            &[Token::Identifier("*/".into(), IdentifierType::Unquoted)],
            &[],
        )?;
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
        test_tokenization(
            "//\n.",
            &[Token::ReservedChar(
                '.',
                TokenIsolation::Isolated,
                TokenIsolation::Isolated,
            )],
            &[],
        )?;
        test_tokenization(
            " . // : \n .",
            &[
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
            ],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn reserved_chars() -> Result<(), Message> {
        test_tokenization(
            ".",
            &[Token::ReservedChar(
                '.',
                TokenIsolation::Isolated,
                TokenIsolation::Isolated,
            )],
            &[],
        )?;
        test_tokenization(
            " . ",
            &[Token::ReservedChar(
                '.',
                TokenIsolation::Isolated,
                TokenIsolation::Isolated,
            )],
            &[],
        )?;
        test_tokenization(
            ". .",
            &[
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
            ],
            &[],
        )?;
        test_tokenization(
            " . . ",
            &[
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
            ],
            &[],
        )?;
        test_tokenization(
            "..",
            &[
                Token::ReservedChar(
                    '.',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                ),
            ],
            &[],
        )?;
        test_tokenization(
            "...",
            &[
                Token::ReservedChar(
                    '.',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                ),
            ],
            &[],
        )?;
        test_tokenization(
            ".,;()[]{}|〈〉",
            &[
                Token::ReservedChar(
                    '.',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    ',',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    ';',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::ReservedChar(
                    '(',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    ')',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::ReservedChar(
                    '[',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    ']',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::ReservedChar(
                    '{',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '}',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::ReservedChar(
                    '|',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::ReservedChar(
                    '〈',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '〉',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                ),
            ],
            &[],
        )?;
        test_tokenization(
            "_",
            &[Token::ReservedChar(
                '_',
                TokenIsolation::Isolated,
                TokenIsolation::Isolated,
            )],
            &[],
        )?;
        test_tokenization(
            "(+).0",
            &[
                Token::ReservedChar(
                    '(',
                    TokenIsolation::Isolated,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    ')',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("0".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn keywords() -> Result<(), Message> {
        test_tokenization("%", &[Token::Keyword("%".into())], &[])?;
        test_tokenization("%x", &[Token::Keyword("%x".into())], &[])?;
        test_tokenization("%for", &[Token::Keyword("%for".into())], &[])?;
        test_tokenization("%+", &[Token::Keyword("%+".into())], &[])?;
        test_tokenization("%%", &[Token::Keyword("%%".into())], &[])?;
        test_tokenization(" %for ", &[Token::Keyword("%for".into())], &[])?;
        test_tokenization(
            "%for %each",
            &[
                Token::Keyword("%for".into()),
                Token::Keyword("%each".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "%for each",
            &[
                Token::Keyword("%for".into()),
                Token::Identifier("each".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "%for_each",
            &[
                Token::Keyword("%for".into()),
                Token::ReservedChar(
                    '_',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("each".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "%for.each",
            &[
                Token::Keyword("%for".into()),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("each".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "%for'each",
            &[
                Token::Keyword("%for'".into()),
                Token::Identifier("each".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn identifiers() -> Result<(), Message> {
        test_tokenization(
            "x",
            &[Token::Identifier("x".into(), IdentifierType::Unquoted)],
            &[],
        )?;
        test_tokenization(
            "+",
            &[Token::Identifier("+".into(), IdentifierType::Unquoted)],
            &[],
        )?;
        test_tokenization(
            "xyz",
            &[Token::Identifier("xyz".into(), IdentifierType::Unquoted)],
            &[],
        )?;
        test_tokenization(
            "+-",
            &[Token::Identifier("+-".into(), IdentifierType::Unquoted)],
            &[],
        )?;
        test_tokenization(
            "a1",
            &[Token::Identifier("a1".into(), IdentifierType::Unquoted)],
            &[],
        )?;
        test_tokenization(
            "a'",
            &[Token::Identifier("a'".into(), IdentifierType::Unquoted)],
            &[],
        )?;
        test_tokenization(
            "a\"",
            &[Token::Identifier("a\"".into(), IdentifierType::Unquoted)],
            &[],
        )?;
        test_tokenization(
            "a''",
            &[Token::Identifier("a''".into(), IdentifierType::Unquoted)],
            &[],
        )?;
        test_tokenization(
            "x y z",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
                Token::Identifier("z".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "x + y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "x+y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "xy+=z",
            &[
                Token::Identifier("xy".into(), IdentifierType::Unquoted),
                Token::Identifier("+=".into(), IdentifierType::Unquoted),
                Token::Identifier("z".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "x' *' y\"",
            &[
                Token::Identifier("x'".into(), IdentifierType::Unquoted),
                Token::Identifier("*'".into(), IdentifierType::Unquoted),
                Token::Identifier("y\"".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "x '*' y\"",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::SingleQuotedString("*".into()),
                Token::Identifier("y\"".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "a'b",
            &[
                Token::Identifier("a'".into(), IdentifierType::Unquoted),
                Token::Identifier("b".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "a'+",
            &[
                Token::Identifier("a'".into(), IdentifierType::Unquoted),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "a_b",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '_',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("b".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "a_+",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '_',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "+_a",
            &[
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '_',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("a".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "a_1",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '_',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Number("1".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "a^2",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '^',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Number("2".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "x.y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "x..y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "x...y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "-.-",
            &[
                Token::Identifier("-".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("-".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "ℕ.0",
            &[
                Token::Identifier("ℕ".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("0".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "ℕ . 0",
            &[
                Token::Identifier("ℕ".into(), IdentifierType::Unquoted),
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
                Token::Identifier("0".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "f(x)",
            &[
                Token::Identifier("f".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '(',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    ')',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::Isolated,
                ),
            ],
            &[],
        )?;
        test_tokenization(
            "f(-)",
            &[
                Token::Identifier("f".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '(',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("-".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    ')',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::Isolated,
                ),
            ],
            &[],
        )?;
        test_tokenization(
            "f(xy,-)",
            &[
                Token::Identifier("f".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '(',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("xy".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    ',',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("-".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    ')',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::Isolated,
                ),
            ],
            &[],
        )?;
        test_tokenization(
            "x @\".\" y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier(".".into(), IdentifierType::Quoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "x@\".\"y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier(".".into(), IdentifierType::Quoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "x@y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[TestDiagnosticMessage {
                range_text: "@".into(),
                severity: Severity::Error,
                msg: "'@' must be followed by a string".into(),
            }],
        )?;
        test_tokenization(
            "x@'.'y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier(".".into(), IdentifierType::Quoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[TestDiagnosticMessage {
                range_text: "@".into(),
                severity: Severity::Error,
                msg: "'@' must be followed by double quotes".into(),
            }],
        )?;
        test_tokenization(
            "@\"x+y.z\"",
            &[Token::Identifier("x+y.z".into(), IdentifierType::Quoted)],
            &[],
        )?;
        test_tokenization(
            "@\"\"",
            &[Token::Identifier("".into(), IdentifierType::Quoted)],
            &[],
        )?;
        test_tokenization(
            "@\"\\n\"",
            &[Token::Identifier("\n".into(), IdentifierType::Quoted)],
            &[],
        )?;
        test_tokenization(
            "abc @\"def",
            &[
                Token::Identifier("abc".into(), IdentifierType::Unquoted),
                Token::Identifier("def".into(), IdentifierType::Quoted),
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
    fn sub_and_superscripts() -> Result<(), Message> {
        test_tokenization(
            "aₙ",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::Identifier("ₙ".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "a'ₙ",
            &[
                Token::Identifier("a'".into(), IdentifierType::Unquoted),
                Token::Identifier("ₙ".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "+ₙ",
            &[
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("ₙ".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "a²",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::Identifier("²".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "a'²",
            &[
                Token::Identifier("a'".into(), IdentifierType::Unquoted),
                Token::Identifier("²".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "+²",
            &[
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("²".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "a⁻¹",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::Identifier("⁻¹".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "+⁻¹",
            &[
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("⁻¹".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "aₙ⁻¹",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::Identifier("ₙ".into(), IdentifierType::Unquoted),
                Token::Identifier("⁻¹".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn numbers() -> Result<(), Message> {
        test_tokenization("0", &[Token::Number("0".into())], &[])?;
        test_tokenization("123", &[Token::Number("123".into())], &[])?;
        test_tokenization("12.345", &[Token::Number("12.345".into())], &[])?;
        test_tokenization("12.", &[Token::Number("12.".into())], &[])?;
        test_tokenization(".345", &[Token::Number(".345".into())], &[])?;
        test_tokenization("1_234_567.89", &[Token::Number("1_234_567.89".into())], &[])?;
        test_tokenization("12.34e5", &[Token::Number("12.34e5".into())], &[])?;
        test_tokenization("12.34e+56", &[Token::Number("12.34e+56".into())], &[])?;
        test_tokenization("12.3e-456", &[Token::Number("12.3e-456".into())], &[])?;
        test_tokenization(".3e-456", &[Token::Number(".3e-456".into())], &[])?;
        test_tokenization("0xf00", &[Token::Number("0xf00".into())], &[])?;
        test_tokenization("0xf00.ba1", &[Token::Number("0xf00.ba1".into())], &[])?;
        test_tokenization("1_foo.bar", &[Token::Number("1_foo.bar".into())], &[])?;
        test_tokenization("12.345", &[Token::Number("12.345".into())], &[])?;
        test_tokenization(
            " 0 1 .2 3. 4 ",
            &[
                Token::Number("0".into()),
                Token::Number("1".into()),
                Token::Number(".2".into()),
                Token::Number("3.".into()),
                Token::Number("4".into()),
            ],
            &[],
        )?;
        test_tokenization(
            " 0 1 . 2 3.4 ",
            &[
                Token::Number("0".into()),
                Token::Number("1".into()),
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
                Token::Identifier("2".into(), IdentifierType::Unquoted),
                Token::Number("3.4".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "0.1.2",
            &[
                Token::Number("0.1".into()),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("2".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "0..1",
            &[
                Token::Number("0".into()),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Number("1".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "0 .. 1",
            &[
                Token::Number("0".into()),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                ),
                Token::Number("1".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "0...1....n",
            &[
                Token::Number("0".into()),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Number("1".into()),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("n".into(), IdentifierType::Unquoted),
            ],
            &[],
        )?;
        test_tokenization(
            "1+2.3e4-5",
            &[
                Token::Number("1".into()),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Number("2.3e4".into()),
                Token::Identifier("-".into(), IdentifierType::Unquoted),
                Token::Number("5".into()),
            ],
            &[],
        )?;
        test_tokenization(
            ".1+.2",
            &[
                Token::Number(".1".into()),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Number(".2".into()),
            ],
            &[],
        )?;
        test_tokenization(
            "(.1 .2)",
            &[
                Token::ReservedChar(
                    '(',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::Number(".1".into()),
                Token::Number(".2".into()),
                Token::ReservedChar(
                    ')',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::Isolated,
                ),
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
                Token::Identifier("abc".into(), IdentifierType::Unquoted),
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
                Token::Identifier("abc".into(), IdentifierType::Unquoted),
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
                Token::Identifier("abc".into(), IdentifierType::Unquoted),
                Token::DoubleQuotedString("def".into()),
                Token::Identifier("ghi".into(), IdentifierType::Unquoted),
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
                Token::Identifier("abc".into(), IdentifierType::Unquoted),
                Token::DoubleQuotedString("def".into()),
                Token::Identifier("ghi".into(), IdentifierType::Unquoted),
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
