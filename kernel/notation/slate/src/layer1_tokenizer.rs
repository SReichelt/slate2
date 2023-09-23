use std::{borrow::Cow, mem::take, ops::Range};

use slate_kernel_notation_generic::{char::*, event::*, event_source::*, event_translator::*};

use crate::chars::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Token<'a> {
    ReservedChar(char, TokenIsolation, TokenIsolation),
    Keyword(Cow<'a, str>),
    Number(Cow<'a, str>),
    String(char, Cow<'a, str>),
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
            single_dot: false,
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
                '%' => {
                    self.source
                        .range_event(RangeClassEvent::Start(RangeClass::Keyword), range.start);
                    start_token(StartedToken::UnquotedIdentifier {
                        content: IdentifierContent::None,
                        post_init: false,
                    });
                }
                '@' => start_token(StartedToken::String {
                    is_quoted_identifier: true,
                    quote_char: '\0',
                    content_start: None,
                    escape_start: None,
                    value: None,
                }),
                '\'' | '"' => {
                    self.source
                        .range_event(RangeClassEvent::Start(RangeClass::String), range.start);
                    start_token(StartedToken::String {
                        is_quoted_identifier: false,
                        quote_char: event,
                        content_start: Some(range.end.clone()),
                        escape_start: None,
                        value: None,
                    });
                }
                c if is_delimiter_char(c) => {
                    if !c.is_whitespace() {
                        let prev = state.prev;
                        let pre_isolation = if prev == '\0' || prev.is_whitespace() {
                            TokenIsolation::Isolated
                        } else if is_pre_weakly_connecting_char(prev) || prev == c {
                            TokenIsolation::WeaklyConnected
                        } else {
                            TokenIsolation::StronglyConnected
                        };
                        start_token(StartedToken::ReservedChar { pre_isolation });
                    }
                }
                c if c.is_ascii_digit() && !state.single_dot => {
                    self.source
                        .range_event(RangeClassEvent::Start(RangeClass::Number), range.start);
                    start_token(StartedToken::Number {
                        number_state: NumberState::BeforeDot,
                    })
                }
                c => start_token(StartedToken::UnquotedIdentifier {
                    content: Self::identifier_content(c),
                    post_init: false,
                }),
            }
        }

        state.single_dot = event == '.' && state.prev != '.';
        state.prev = event;
    }

    fn next_pass(
        self,
        mut state: Self::State,
        end_marker: &Self::Marker,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        let handled = self.handle_char_in_current_state(
            &mut state,
            '\0',
            &(end_marker..end_marker),
            &mut out,
        );
        assert!(!handled);
        assert!(state.started_token.is_none());
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
                    self.source
                        .range_event(RangeClassEvent::End(RangeClass::Comment), range.start);
                    state.started_token = None;
                    return false;
                }
            }

            StartedToken::BlockComment {
                nesting_level,
                slash_seen,
                asterisk_seen,
            } => {
                if c == '\0' {
                    self.source.diagnostic(
                        &*token_start..range.start,
                        Severity::Error,
                        format!("unterminated comment"),
                    );
                    self.source
                        .range_event(RangeClassEvent::End(RangeClass::Comment), range.end);
                    state.started_token = None;
                    return false;
                }
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
                            self.source
                                .range_event(RangeClassEvent::End(RangeClass::Comment), range.end);
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
                                self.source
                                    .range_event(RangeClassEvent::End(RangeClass::Number), marker);
                                out(
                                    Token::ReservedChar(
                                        '.',
                                        TokenIsolation::StronglyConnected,
                                        TokenIsolation::WeaklyConnected,
                                    ),
                                    &*marker..range.start,
                                );
                                *state = TokenizerState {
                                    dot_number_allowed: false,
                                    started_token: None,
                                    ..*state
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
                    self.source
                        .range_event(RangeClassEvent::End(RangeClass::Number), range.start);
                    *state = TokenizerState {
                        dot_number_allowed: c != '.',
                        started_token: None,
                        ..*state
                    };
                    return false;
                }
            }

            StartedToken::String {
                is_quoted_identifier,
                quote_char,
                content_start,
                escape_start,
                value,
            } => {
                if let Some(content_start) = content_start {
                    let mut end_string = |token_range: Range<&Src::Marker>| {
                        let final_value = if let Some(value) = value {
                            Cow::Owned(take(value))
                        } else {
                            self.source.slice(&*content_start..range.start)
                        };
                        let token = if *is_quoted_identifier {
                            Token::Identifier(final_value, IdentifierType::Quoted)
                        } else {
                            Token::String(*quote_char, final_value)
                        };
                        let end = token_range.end;
                        out(token, token_range);
                        if !*is_quoted_identifier {
                            self.source
                                .range_event(RangeClassEvent::End(RangeClass::String), end);
                        }
                    };

                    if c.is_ascii_control() && c != '\t' {
                        self.source.diagnostic(
                            &*token_start..range.start,
                            Severity::Error,
                            format!("unterminated string"),
                        );
                        end_string(&*token_start..range.start);
                        *state = TokenizerState {
                            dot_number_allowed: false,
                            started_token: None,
                            ..*state
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

                    if c == *quote_char {
                        end_string(&*token_start..range.end);
                        *state = TokenizerState {
                            dot_number_allowed: false,
                            started_token: None,
                            ..*state
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
                        *quote_char = c;
                        if c != '"' {
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
                            dot_number_allowed: false,
                            started_token: None,
                            ..*state
                        };
                        return false;
                    }
                }
            }

            StartedToken::UnquotedIdentifier { content, post_init } => {
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
                    let is_keyword = identifier.starts_with('%');
                    let token = if is_keyword {
                        Token::Keyword(identifier)
                    } else {
                        Token::Identifier(identifier, IdentifierType::Unquoted)
                    };
                    out(token, &*token_start..range.start);
                    if is_keyword {
                        self.source
                            .range_event(RangeClassEvent::End(RangeClass::Keyword), range.start);
                    }
                    *state = TokenizerState {
                        dot_number_allowed: *content == IdentifierContent::Symbol,
                        started_token: None,
                        ..*state
                    };
                    return false;
                } else if !*post_init && state.prev == '/' {
                    if c == '/' {
                        *token = StartedToken::LineComment;
                        self.source
                            .range_event(RangeClassEvent::Start(RangeClass::Comment), token_start);
                    } else if c == '*' {
                        *token = StartedToken::BlockComment {
                            nesting_level: 0,
                            slash_seen: false,
                            asterisk_seen: false,
                        };
                        self.source
                            .range_event(RangeClassEvent::Start(RangeClass::Comment), token_start);
                    } else {
                        *post_init = true;
                    }
                } else {
                    *post_init = true;
                }
            }

            StartedToken::ReservedChar { pre_isolation } => {
                let ch = state.prev;
                if ch == '.' && state.dot_number_allowed && c.is_ascii_digit() {
                    self.source
                        .range_event(RangeClassEvent::Start(RangeClass::Number), token_start);
                    *token = StartedToken::Number {
                        number_state: NumberState::AfterDot(Some(range.start.clone())),
                    };
                } else {
                    let post_isolation = if c == '\0' || c.is_whitespace() {
                        TokenIsolation::Isolated
                    } else if is_post_weakly_connecting_char(c) || c == ch {
                        TokenIsolation::WeaklyConnected
                    } else {
                        TokenIsolation::StronglyConnected
                    };
                    out(
                        Token::ReservedChar(ch, *pre_isolation, post_isolation),
                        &*token_start..range.start,
                    );
                    *state = TokenizerState {
                        dot_number_allowed: ch == ',' || ch == ';' || is_opening_parenthesis(ch),
                        started_token: None,
                        ..*state
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
    single_dot: bool,
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
        quote_char: char,
        content_start: Option<Marker>,
        escape_start: Option<Marker>,
        value: Option<String>,
    },
    UnquotedIdentifier {
        content: IdentifierContent,
        post_init: bool,
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
    // TODO: We probably want to distinguish between different classes of alphanumeric content, so
    //       that things like `λa` are two separate tokens.
    Alphanumeric,
    Symbol,
    Subscript,
    Superscript,
}

#[cfg(test)]
mod tests {
    use slate_kernel_notation_generic::{
        char_slice::{test_helpers::*, *},
        event::test_helpers::*,
        event_source::test_helpers::*,
    };

    use super::*;

    #[test]
    fn whitespace() -> Result<(), Message> {
        test_tokenization("", &[], &[], None)?;
        test_tokenization(" ", &[], &[], None)?;
        test_tokenization("\t", &[], &[], None)?;
        test_tokenization(
            " \n\t\r\n ",
            &[],
            &[],
            Some(vec![RangeClassTreeNode::Text(" \n\t\r\n ")]),
        )?;
        test_tokenization(
            "/**/",
            &[],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("/**/")],
            )]),
        )?;
        test_tokenization(
            "/* */",
            &[],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("/* */")],
            )]),
        )?;
        test_tokenization(
            " /* abc \n def */ . /* ghi */ ",
            &[Token::ReservedChar(
                '.',
                TokenIsolation::Isolated,
                TokenIsolation::Isolated,
            )],
            &[],
            Some(vec![
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::Comment,
                    vec![RangeClassTreeNode::Text("/* abc \n def */")],
                ),
                RangeClassTreeNode::Text(" . "),
                RangeClassTreeNode::Range(
                    RangeClass::Comment,
                    vec![RangeClassTreeNode::Text("/* ghi */")],
                ),
                RangeClassTreeNode::Text(" "),
            ]),
        )?;
        test_tokenization(
            "/***/",
            &[],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("/***/")],
            )]),
        )?;
        test_tokenization(
            "/*/**/*/",
            &[],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("/*/**/*/")],
            )]),
        )?;
        test_tokenization(
            "/**/*/",
            &[Token::Identifier("*/".into(), IdentifierType::Unquoted)],
            &[],
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::Comment,
                    vec![RangeClassTreeNode::Text("/**/")],
                ),
                RangeClassTreeNode::Text("*/"),
            ]),
        )?;
        test_tokenization(
            "/* // */",
            &[],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("/* // */")],
            )]),
        )?;
        test_tokenization(
            "/*",
            &[],
            &[TestDiagnosticMessage {
                range_text: "/*".into(),
                severity: Severity::Error,
                msg: "unterminated comment".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("/*")],
            )]),
        )?;
        test_tokenization(
            " /*/ ",
            &[],
            &[TestDiagnosticMessage {
                range_text: "/*/ ".into(),
                severity: Severity::Error,
                msg: "unterminated comment".into(),
            }],
            Some(vec![
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::Comment,
                    vec![RangeClassTreeNode::Text("/*/ ")],
                ),
            ]),
        )?;
        test_tokenization(
            "/*/**/",
            &[],
            &[TestDiagnosticMessage {
                range_text: "/*/**/".into(),
                severity: Severity::Error,
                msg: "unterminated comment".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("/*/**/")],
            )]),
        )?;
        test_tokenization(
            "/*//*/",
            &[],
            &[TestDiagnosticMessage {
                range_text: "/*//*/".into(),
                severity: Severity::Error,
                msg: "unterminated comment".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("/*//*/")],
            )]),
        )?;
        test_tokenization(
            "//",
            &[],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("//")],
            )]),
        )?;
        test_tokenization(
            "///",
            &[],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Comment,
                vec![RangeClassTreeNode::Text("///")],
            )]),
        )?;
        test_tokenization(
            "//\n",
            &[],
            &[],
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::Comment,
                    vec![RangeClassTreeNode::Text("//")],
                ),
                RangeClassTreeNode::Text("\n"),
            ]),
        )?;
        test_tokenization(
            "//\n.",
            &[Token::ReservedChar(
                '.',
                TokenIsolation::Isolated,
                TokenIsolation::Isolated,
            )],
            &[],
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::Comment,
                    vec![RangeClassTreeNode::Text("//")],
                ),
                RangeClassTreeNode::Text("\n."),
            ]),
        )?;
        test_tokenization(
            " . // : \n .",
            &[
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Text(" . "),
                RangeClassTreeNode::Range(
                    RangeClass::Comment,
                    vec![RangeClassTreeNode::Text("// : ")],
                ),
                RangeClassTreeNode::Text("\n ."),
            ]),
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
            None,
        )?;
        test_tokenization(
            " . ",
            &[Token::ReservedChar(
                '.',
                TokenIsolation::Isolated,
                TokenIsolation::Isolated,
            )],
            &[],
            None,
        )?;
        test_tokenization(
            ". .",
            &[
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            " . . ",
            &[
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
            ],
            &[],
            None,
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
            None,
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
            None,
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
            None,
        )?;
        test_tokenization(
            "||",
            &[
                Token::ReservedChar(
                    '|',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ),
                Token::ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                ),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "_",
            &[Token::ReservedChar(
                '_',
                TokenIsolation::Isolated,
                TokenIsolation::Isolated,
            )],
            &[],
            None,
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
            None,
        )?;
        Ok(())
    }

    #[test]
    fn keywords() -> Result<(), Message> {
        test_tokenization(
            "%",
            &[Token::Keyword("%".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Keyword,
                vec![RangeClassTreeNode::Text("%")],
            )]),
        )?;
        test_tokenization(
            "%x",
            &[Token::Keyword("%x".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Keyword,
                vec![RangeClassTreeNode::Text("%x")],
            )]),
        )?;
        test_tokenization(
            "%for",
            &[Token::Keyword("%for".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Keyword,
                vec![RangeClassTreeNode::Text("%for")],
            )]),
        )?;
        test_tokenization(
            "%+",
            &[Token::Keyword("%+".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Keyword,
                vec![RangeClassTreeNode::Text("%+")],
            )]),
        )?;
        test_tokenization(
            "%%",
            &[Token::Keyword("%%".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Keyword,
                vec![RangeClassTreeNode::Text("%%")],
            )]),
        )?;
        test_tokenization(
            " %for ",
            &[Token::Keyword("%for".into())],
            &[],
            Some(vec![
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%for")],
                ),
                RangeClassTreeNode::Text(" "),
            ]),
        )?;
        test_tokenization(
            "%for %each",
            &[
                Token::Keyword("%for".into()),
                Token::Keyword("%each".into()),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%for")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%each")],
                ),
            ]),
        )?;
        test_tokenization(
            "%for each",
            &[
                Token::Keyword("%for".into()),
                Token::Identifier("each".into(), IdentifierType::Unquoted),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%for")],
                ),
                RangeClassTreeNode::Text(" each"),
            ]),
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
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%for")],
                ),
                RangeClassTreeNode::Text("_each"),
            ]),
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
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%for")],
                ),
                RangeClassTreeNode::Text(".each"),
            ]),
        )?;
        test_tokenization(
            "%for'each",
            &[
                Token::Keyword("%for'".into()),
                Token::Identifier("each".into(), IdentifierType::Unquoted),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%for'")],
                ),
                RangeClassTreeNode::Text("each"),
            ]),
        )?;
        Ok(())
    }

    #[test]
    fn identifiers() -> Result<(), Message> {
        test_tokenization(
            "x",
            &[Token::Identifier("x".into(), IdentifierType::Unquoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "+",
            &[Token::Identifier("+".into(), IdentifierType::Unquoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "xyz",
            &[Token::Identifier("xyz".into(), IdentifierType::Unquoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "+-",
            &[Token::Identifier("+-".into(), IdentifierType::Unquoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "a1",
            &[Token::Identifier("a1".into(), IdentifierType::Unquoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "a'",
            &[Token::Identifier("a'".into(), IdentifierType::Unquoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "a\"",
            &[Token::Identifier("a\"".into(), IdentifierType::Unquoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "a''",
            &[Token::Identifier("a''".into(), IdentifierType::Unquoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "+/*",
            &[Token::Identifier("+/*".into(), IdentifierType::Unquoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "x y z",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
                Token::Identifier("z".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "x + y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "x+y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "xy+=z",
            &[
                Token::Identifier("xy".into(), IdentifierType::Unquoted),
                Token::Identifier("+=".into(), IdentifierType::Unquoted),
                Token::Identifier("z".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "x' *' y\"",
            &[
                Token::Identifier("x'".into(), IdentifierType::Unquoted),
                Token::Identifier("*'".into(), IdentifierType::Unquoted),
                Token::Identifier("y\"".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "x '*' y\"",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::String('\'', "*".into()),
                Token::Identifier("y\"".into(), IdentifierType::Unquoted),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Text("x "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("'*'")],
                ),
                RangeClassTreeNode::Text(" y\""),
            ]),
        )?;
        test_tokenization(
            "a'b",
            &[
                Token::Identifier("a'".into(), IdentifierType::Unquoted),
                Token::Identifier("b".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "a'+",
            &[
                Token::Identifier("a'".into(), IdentifierType::Unquoted),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
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
            None,
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
            None,
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
            None,
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
            Some(vec![
                RangeClassTreeNode::Text("a_"),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("1")]),
            ]),
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
            Some(vec![
                RangeClassTreeNode::Text("a^"),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("2")]),
            ]),
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
            None,
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
            None,
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
            None,
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
            None,
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
            None,
        )?;
        test_tokenization(
            "ℕ .0",
            &[
                Token::Identifier("ℕ".into(), IdentifierType::Unquoted),
                Token::ReservedChar(
                    '.',
                    TokenIsolation::Isolated,
                    TokenIsolation::StronglyConnected,
                ),
                Token::Identifier("0".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
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
            None,
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
            None,
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
            None,
        )?;
        test_tokenization(
            "x @\".\" y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier(".".into(), IdentifierType::Quoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "x@\".\"y",
            &[
                Token::Identifier("x".into(), IdentifierType::Unquoted),
                Token::Identifier(".".into(), IdentifierType::Quoted),
                Token::Identifier("y".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
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
            None,
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
            None,
        )?;
        test_tokenization(
            "@\"x+y.z\"",
            &[Token::Identifier("x+y.z".into(), IdentifierType::Quoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "@\"\"",
            &[Token::Identifier("".into(), IdentifierType::Quoted)],
            &[],
            None,
        )?;
        test_tokenization(
            "@\"\\n\"",
            &[Token::Identifier("\n".into(), IdentifierType::Quoted)],
            &[],
            None,
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
            None,
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
            None,
        )?;
        test_tokenization(
            "a'ₙ",
            &[
                Token::Identifier("a'".into(), IdentifierType::Unquoted),
                Token::Identifier("ₙ".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "+ₙ",
            &[
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("ₙ".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "a²",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::Identifier("²".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "a'²",
            &[
                Token::Identifier("a'".into(), IdentifierType::Unquoted),
                Token::Identifier("²".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "+²",
            &[
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("²".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "a⁻¹",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::Identifier("⁻¹".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "+⁻¹",
            &[
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Identifier("⁻¹".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        test_tokenization(
            "aₙ⁻¹",
            &[
                Token::Identifier("a".into(), IdentifierType::Unquoted),
                Token::Identifier("ₙ".into(), IdentifierType::Unquoted),
                Token::Identifier("⁻¹".into(), IdentifierType::Unquoted),
            ],
            &[],
            None,
        )?;
        Ok(())
    }

    #[test]
    fn numbers() -> Result<(), Message> {
        test_tokenization(
            "0",
            &[Token::Number("0".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("0")],
            )]),
        )?;
        test_tokenization(
            "123",
            &[Token::Number("123".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("123")],
            )]),
        )?;
        test_tokenization(
            "12.345",
            &[Token::Number("12.345".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("12.345")],
            )]),
        )?;
        test_tokenization(
            "12.",
            &[Token::Number("12.".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("12.")],
            )]),
        )?;
        test_tokenization(
            ".345",
            &[Token::Number(".345".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text(".345")],
            )]),
        )?;
        test_tokenization(
            "1_234_567.89",
            &[Token::Number("1_234_567.89".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("1_234_567.89")],
            )]),
        )?;
        test_tokenization(
            "12.34e5",
            &[Token::Number("12.34e5".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("12.34e5")],
            )]),
        )?;
        test_tokenization(
            "12.34e+56",
            &[Token::Number("12.34e+56".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("12.34e+56")],
            )]),
        )?;
        test_tokenization(
            "12.3e-456",
            &[Token::Number("12.3e-456".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("12.3e-456")],
            )]),
        )?;
        test_tokenization(
            ".3e-456",
            &[Token::Number(".3e-456".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text(".3e-456")],
            )]),
        )?;
        test_tokenization(
            "0xf00",
            &[Token::Number("0xf00".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("0xf00")],
            )]),
        )?;
        test_tokenization(
            "0xf00.ba1",
            &[Token::Number("0xf00.ba1".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("0xf00.ba1")],
            )]),
        )?;
        test_tokenization(
            "1_foo.bar",
            &[Token::Number("1_foo.bar".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::Number,
                vec![RangeClassTreeNode::Text("1_foo.bar")],
            )]),
        )?;
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
            Some(vec![
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("0")]),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("1")]),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text(".2")]),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("3.")]),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("4")]),
                RangeClassTreeNode::Text(" "),
            ]),
        )?;
        test_tokenization(
            " 0 1 . 2 3.4 ",
            &[
                Token::Number("0".into()),
                Token::Number("1".into()),
                Token::ReservedChar('.', TokenIsolation::Isolated, TokenIsolation::Isolated),
                Token::Number("2".into()),
                Token::Number("3.4".into()),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("0")]),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("1")]),
                RangeClassTreeNode::Text(" . "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("2")]),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::Number,
                    vec![RangeClassTreeNode::Text("3.4")],
                ),
                RangeClassTreeNode::Text(" "),
            ]),
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
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::Number,
                    vec![RangeClassTreeNode::Text("0.1")],
                ),
                RangeClassTreeNode::Text(".2"),
            ]),
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
            Some(vec![
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("0")]),
                RangeClassTreeNode::Text(".."),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("1")]),
            ]),
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
            Some(vec![
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("0")]),
                RangeClassTreeNode::Text(" .. "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("1")]),
            ]),
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
            Some(vec![
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("0")]),
                RangeClassTreeNode::Text("..."),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("1")]),
                RangeClassTreeNode::Text("....n"),
            ]),
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
            Some(vec![
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("1")]),
                RangeClassTreeNode::Text("+"),
                RangeClassTreeNode::Range(
                    RangeClass::Number,
                    vec![RangeClassTreeNode::Text("2.3e4")],
                ),
                RangeClassTreeNode::Text("-"),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("5")]),
            ]),
        )?;
        test_tokenization(
            ".1+.2",
            &[
                Token::Number(".1".into()),
                Token::Identifier("+".into(), IdentifierType::Unquoted),
                Token::Number(".2".into()),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text(".1")]),
                RangeClassTreeNode::Text("+"),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text(".2")]),
            ]),
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
            Some(vec![
                RangeClassTreeNode::Text("("),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text(".1")]),
                RangeClassTreeNode::Text("+"),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text(".2")]),
                RangeClassTreeNode::Text(")"),
            ]),
        )?;
        Ok(())
    }

    #[test]
    fn strings() -> Result<(), Message> {
        test_tokenization(
            "''",
            &[Token::String('\'', "".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("''")],
            )]),
        )?;
        test_tokenization(
            "'abc'",
            &[Token::String('\'', "abc".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("'abc'")],
            )]),
        )?;
        test_tokenization(
            "'\"'",
            &[Token::String('\'', "\"".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("'\"'")],
            )]),
        )?;
        test_tokenization(
            "'/*'",
            &[Token::String('\'', "/*".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("'/*'")],
            )]),
        )?;
        test_tokenization(
            "\"\"",
            &[Token::String('"', "".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\"")],
            )]),
        )?;
        test_tokenization(
            "\"abc\"",
            &[Token::String('"', "abc".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"abc\"")],
            )]),
        )?;
        test_tokenization(
            "\"'\"",
            &[Token::String('"', "'".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"'\"")],
            )]),
        )?;
        test_tokenization(
            "\"/*\"",
            &[Token::String('"', "/*".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"/*\"")],
            )]),
        )?;
        test_tokenization(
            "'abc'\"abc\"",
            &[
                Token::String('\'', "abc".into()),
                Token::String('"', "abc".into()),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("'abc'")],
                ),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"abc\"")],
                ),
            ]),
        )?;
        test_tokenization(
            "\"abc\"\"abc\"",
            &[
                Token::String('"', "abc".into()),
                Token::String('"', "abc".into()),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"abc\"")],
                ),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"abc\"")],
                ),
            ]),
        )?;
        test_tokenization(
            " 'abc' \"abc\" ",
            &[
                Token::String('\'', "abc".into()),
                Token::String('"', "abc".into()),
            ],
            &[],
            Some(vec![
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("'abc'")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"abc\"")],
                ),
                RangeClassTreeNode::Text(" "),
            ]),
        )?;
        test_tokenization(
            "\"abc /*def*/ ghi\"",
            &[Token::String('"', "abc /*def*/ ghi".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"abc /*def*/ ghi\"")],
            )]),
        )?;
        test_tokenization(
            "'\\n'",
            &[Token::String('\'', "\n".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("'\\n'")],
            )]),
        )?;
        test_tokenization(
            "'\\\''",
            &[Token::String('\'', "'".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("'\\\''")],
            )]),
        )?;
        test_tokenization(
            "'\\\\'",
            &[Token::String('\'', "\\".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("'\\\\'")],
            )]),
        )?;
        test_tokenization(
            "\"\\n\"",
            &[Token::String('"', "\n".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\n\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\\"\"",
            &[Token::String('"', "\"".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\\"\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\\\\"",
            &[Token::String('"', "\\".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\\\\"")],
            )]),
        )?;
        test_tokenization(
            "\"abc\\ndef\"",
            &[Token::String('"', "abc\ndef".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"abc\\ndef\"")],
            )]),
        )?;
        test_tokenization(
            "\"abc\\r\\n\\tdef\\0\"",
            &[Token::String('"', "abc\r\n\tdef\0".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"abc\\r\\n\\tdef\\0\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\x17\"",
            &[Token::String('"', "\x17".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\x17\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\x0c\"",
            &[Token::String('"', "\x0c".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\x0c\"")],
            )]),
        )?;
        test_tokenization(
            "\"abc\\x17def\"",
            &[Token::String('"', "abc\x17def".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"abc\\x17def\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\u{17}\"",
            &[Token::String('"', "\u{17}".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\u{17}\"")],
            )]),
        )?;
        test_tokenization(
            "\"abc\\u{17}def\"",
            &[Token::String('"', "abc\u{17}def".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"abc\\u{17}def\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\u42\"",
            &[Token::String('"', "42".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u".into(),
                severity: Severity::Error,
                msg: "'\\u' must be followed by a hexadecimal number in braces".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\u42\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\u{}\"",
            &[Token::String('"', "".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u{}".into(),
                severity: Severity::Error,
                msg: "'' is not a valid Unicode character code".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\u{}\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\u{e3a}\"",
            &[Token::String('"', "\u{e3a}".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\u{e3a}\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\u{e3g}\"",
            &[Token::String('"', "g}".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u{e3".into(),
                severity: Severity::Error,
                msg: "'\\u' must be followed by a hexadecimal number in braces".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\u{e3g}\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\u{d800}\"",
            &[Token::String('"', "".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u{d800}".into(),
                severity: Severity::Error,
                msg: "'d800' is not a valid Unicode character code".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\u{d800}\"")],
            )]),
        )?;
        test_tokenization(
            "\"\\u{10000}\"",
            &[Token::String('"', "\u{10000}".into())],
            &[],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"\\u{10000}\"")],
            )]),
        )?;
        test_tokenization(
            "\"abc\\u{10000000}def\"",
            &[Token::String('"', "abcdef".into())],
            &[TestDiagnosticMessage {
                range_text: "\\u{10000000}".into(),
                severity: Severity::Error,
                msg: "'10000000' is not a valid Unicode character code".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"abc\\u{10000000}def\"")],
            )]),
        )?;
        test_tokenization(
            "\"a\\bc\"",
            &[Token::String('"', "abc".into())],
            &[TestDiagnosticMessage {
                range_text: "\\b".into(),
                severity: Severity::Error,
                msg: "invalid escape sequence".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"a\\bc\"")],
            )]),
        )?;
        test_tokenization(
            "\"",
            &[Token::String('"', "".into())],
            &[TestDiagnosticMessage {
                range_text: "\"".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
            Some(vec![RangeClassTreeNode::Range(
                RangeClass::String,
                vec![RangeClassTreeNode::Text("\"")],
            )]),
        )?;
        test_tokenization(
            " abc \" def ",
            &[
                Token::Identifier("abc".into(), IdentifierType::Unquoted),
                Token::String('"', " def ".into()),
            ],
            &[TestDiagnosticMessage {
                range_text: "\" def ".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
            Some(vec![
                RangeClassTreeNode::Text(" abc "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\" def ")],
                ),
            ]),
        )?;
        test_tokenization(
            " abc \" def \\",
            &[
                Token::Identifier("abc".into(), IdentifierType::Unquoted),
                Token::String('"', " def ".into()),
            ],
            &[TestDiagnosticMessage {
                range_text: "\" def \\".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
            Some(vec![
                RangeClassTreeNode::Text(" abc "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\" def \\")],
                ),
            ]),
        )?;
        test_tokenization(
            "abc \"def\nghi",
            &[
                Token::Identifier("abc".into(), IdentifierType::Unquoted),
                Token::String('"', "def".into()),
                Token::Identifier("ghi".into(), IdentifierType::Unquoted),
            ],
            &[TestDiagnosticMessage {
                range_text: "\"def".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
            Some(vec![
                RangeClassTreeNode::Text("abc "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"def")],
                ),
                RangeClassTreeNode::Text("\nghi"),
            ]),
        )?;
        test_tokenization(
            "abc \"def\\\nghi",
            &[
                Token::Identifier("abc".into(), IdentifierType::Unquoted),
                Token::String('"', "def".into()),
                Token::Identifier("ghi".into(), IdentifierType::Unquoted),
            ],
            &[TestDiagnosticMessage {
                range_text: "\"def\\".into(),
                severity: Severity::Error,
                msg: "unterminated string".into(),
            }],
            Some(vec![
                RangeClassTreeNode::Text("abc "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"def\\")],
                ),
                RangeClassTreeNode::Text("\nghi"),
            ]),
        )?;
        Ok(())
    }

    fn test_tokenization(
        input: &str,
        expected_tokens: &[Token],
        expected_diagnostics: &[TestDiagnosticMessage],
        expected_ranges: Option<RangeClassTree>,
    ) -> Result<(), Message> {
        let mut tokens = Vec::new();
        let char_sink = TranslatorInst::new(Tokenizer, &mut tokens);
        let diag_sink = DiagnosticsRecorder::new(input);
        let source = CharSliceEventSource::new(input, &diag_sink)?;
        source.run(char_sink);
        assert_eq!(tokens, expected_tokens);
        let (diagnostics, range_events) = diag_sink.results();
        assert_eq!(diagnostics, expected_diagnostics);
        if let Some(expected_ranges) = expected_ranges {
            assert_eq!((range_events, input.len()), expected_ranges.into_events());
        } else {
            assert_eq!(range_events, []);
        }
        Ok(())
    }
}
