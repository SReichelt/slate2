use std::{borrow::Cow, fmt::Debug, ops::Range};

use lang_def::{mem_serializable::*, parser::*};

use super::chars::*;

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub enum Token<'a> {
    ReservedChar(char, TokenIsolation, TokenIsolation),
    Keyword(Cow<'a, str>),
    Number(Cow<'a, str>),
    String(char, Cow<'a, str>),
    Ident(Cow<'a, str>, IdentifierType),
}

#[derive(MemSerializable)]
pub struct Tokenizer {
    prev: char,
    dot_seen: bool,
    dots_seen: bool,
    dot_number_allowed: bool,
}

impl Tokenizer {
    pub fn new() -> Self {
        Tokenizer {
            prev: '\0',
            dot_seen: false,
            dots_seen: false,
            dot_number_allowed: true,
        }
    }
}

impl<'a, IF: ParserInterface<In = char, Out = Token<'a>, Input: CharParserInput<'a>>> Parser<IF>
    for Tokenizer
{
    fn parse(&mut self, interface: &mut IF) -> bool {
        let input = interface.input();
        let Some(ch) = input.next() else {
            return true;
        };

        let mut span = ch.span();
        let ch = *ch;

        match ch {
            '/' => {
                if let Some(ch2) = input.next_if(|&ch2| ch2 == '/' || ch2 == '*') {
                    span.end = ch2.span().end;
                    let ch2 = *ch2;
                    self.prev = ch2;
                    if ch2 == '/' {
                        self.process_line_comment(interface, span);
                    } else {
                        self.process_block_comment(interface, span);
                    }
                    return false;
                }
            }
            '%' => {
                if let Some(ch2) = input.next_if(|&ch2| {
                    !is_delimiter_char(ch2)
                        && IdentifierContent::get(ch2) == IdentifierContent::Alphanumeric
                }) {
                    span.end = ch2.span().end;
                    self.prev = *ch2;
                    self.process_unquoted_identifier(
                        interface,
                        span,
                        IdentifierContent::Alphanumeric,
                        true,
                    );
                    return false;
                }
            }
            '@' => {
                if let Some(ch2) = input.next_if(|&ch2| ch2 == '"') {
                    span.end = ch2.span().end;
                    self.prev = *ch2;
                    self.process_string(interface, span, *ch2, true);
                    return false;
                }
            }
            '\'' | '"' => {
                self.prev = ch;
                self.process_string(interface, span, ch, false);
                return false;
            }
            '`' => {
                self.prev = ch;
                interface.error(
                    span.clone(),
                    Some(ErrorKind::SyntaxError),
                    format!("the backtick character is reserved for future use"),
                );
                return false;
            }
            '.' => {
                if self.dot_number_allowed && input.check_next(|ch2| ch2.is_ascii_digit()) {
                    self.prev = ch;
                    self.process_number(interface, span, true);
                    return false;
                }
            }
            _ => {}
        }

        if is_delimiter_char(ch) {
            if !ch.is_whitespace() {
                let pre_isolation = TokenIsolation::get_pre_isolation(ch, self.prev);
                let next = input.look_ahead().as_deref().copied().unwrap_or('\0');
                let post_isolation = TokenIsolation::get_post_isolation(ch, next);
                interface.out(span, Token::ReservedChar(ch, pre_isolation, post_isolation));
                self.dot_number_allowed = ch == ',' || ch == ';' || is_opening_parenthesis(ch);
                if ch == '.' {
                    if self.dot_seen {
                        self.dots_seen = true;
                    } else {
                        self.dot_seen = true;
                    }
                } else {
                    self.dot_seen = false;
                    self.dots_seen = false;
                }
            }
            self.prev = ch;
        } else if ch.is_ascii_digit() && (!self.dot_seen || self.dots_seen) {
            self.prev = ch;
            self.process_number(interface, span, false);
        } else {
            self.prev = ch;
            self.process_unquoted_identifier(interface, span, IdentifierContent::get(ch), false);
        }

        false
    }
}

impl Tokenizer {
    fn process_unquoted_identifier<
        'a,
        IF: ParserInterface<In = char, Out = Token<'a>, Input: CharParserInput<'a>>,
    >(
        &mut self,
        interface: &mut IF,
        mut span: Range<IF::Pos>,
        content: IdentifierContent,
        is_keyword: bool,
    ) {
        let input = interface.input();

        while let Some(ch) = input.next_if(|&ch| {
            !is_delimiter_char(ch)
                && (is_prime_char(ch)
                    || (!is_prime_char(self.prev) && IdentifierContent::get(ch) == content))
        }) {
            span.end = ch.span().end;
            self.prev = *ch;
        }

        let identifier = input.span_str(span.clone());
        let token = if is_keyword {
            Token::Keyword(identifier)
        } else {
            Token::Ident(identifier, IdentifierType::Unquoted)
        };
        interface.out(span.clone(), token);
        if is_keyword {
            interface.span_desc(span, SpanDesc::Keyword);
        }
        self.dot_seen = false;
        self.dots_seen = false;
        self.dot_number_allowed = content == IdentifierContent::Symbol;
    }

    fn process_line_comment<
        'a,
        IF: ParserInterface<In = char, Out = Token<'a>, Input: CharParserInput<'a>>,
    >(
        &mut self,
        interface: &mut IF,
        mut span: Range<IF::Pos>,
    ) {
        let input = interface.input();
        loop {
            let Some(ch) = input.next() else {
                self.prev = '\0';
                break;
            };
            if *ch == '\r' || *ch == '\n' {
                self.prev = *ch;
                break;
            }
            span.end = ch.span().end;
        }
        interface.span_desc(span, SpanDesc::Comment);
        self.dot_number_allowed = true;
    }

    fn process_block_comment<
        'a,
        IF: ParserInterface<In = char, Out = Token<'a>, Input: CharParserInput<'a>>,
    >(
        &mut self,
        interface: &mut IF,
        mut span: Range<IF::Pos>,
    ) {
        // Declare block comment delimiters as parentheses, to enable folding in IDEs.
        interface.span_desc(span.clone(), SpanDesc::ParenStart);
        let mut nesting_level: usize = 0;
        loop {
            let Some(ch) = interface.input().next() else {
                loop {
                    interface.span_desc(span.end.clone(), SpanDesc::ParenEnd);
                    if nesting_level == 0 {
                        break;
                    }
                    nesting_level -= 1;
                }
                interface.error(
                    span.clone(),
                    Some(ErrorKind::SyntaxError),
                    format!("unterminated comment"),
                );
                self.prev = '\0';
                break;
            };
            span.end = ch.span().end;
            match *ch {
                '/' => {
                    if let Some(ch2) = interface.input().next_if(|&ch2| ch2 == '*') {
                        span.end = ch2.span().end;
                        interface.span_desc(&ch..&ch2, SpanDesc::ParenStart);
                        nesting_level += 1;
                    }
                }
                '*' => {
                    if let Some(ch2) = interface.input().next_if(|&ch2| ch2 == '/') {
                        span.end = ch2.span().end;
                        interface.span_desc(&ch..&ch2, SpanDesc::ParenEnd);
                        if nesting_level == 0 {
                            self.prev = *ch;
                            break;
                        }
                        nesting_level -= 1;
                    }
                }
                _ => {}
            }
        }
        interface.span_desc(span, SpanDesc::Comment);
        self.dot_number_allowed = true;
    }

    fn process_number<
        'a,
        IF: ParserInterface<In = char, Out = Token<'a>, Input: CharParserInput<'a>>,
    >(
        &mut self,
        interface: &mut IF,
        mut span: Range<IF::Pos>,
        mut after_dot: bool,
    ) {
        self.dot_number_allowed = true;

        let input = interface.input();
        let mut in_exponent = false;

        loop {
            let Some(mut ch) = input.look_ahead() else {
                self.prev = '\0';
                break;
            };

            if *ch == '.' {
                if after_dot {
                    self.dot_number_allowed = false;
                    break;
                }
                if ch.check_next(|&ch2| ch2 == '.') {
                    break;
                }
                after_dot = true;
            } else if !(ch.is_ascii_alphanumeric() || *ch == '_') {
                break;
            }

            let ch = ch.consume();
            span.end = ch.span().end;
            let ch = *ch;
            self.prev = ch;

            if after_dot && !in_exponent && (ch == 'E' || ch == 'e') {
                if let Some(ch2) = input.next_if(|&ch2| ch2 == '+' || ch2 == '-') {
                    span.end = ch2.span().end;
                    self.prev = *ch2;
                }
                in_exponent = true;
            }
        }

        let number = input.span_str(span.clone());
        interface.out_with_desc(span, Token::Number(number), SpanDesc::Number);
        self.dot_seen = false;
        self.dots_seen = false;
    }

    fn process_string<
        'a,
        IF: ParserInterface<In = char, Out = Token<'a>, Input: CharParserInput<'a>>,
    >(
        &mut self,
        interface: &mut IF,
        mut span: Range<IF::Pos>,
        quote: char,
        is_quoted_identifier: bool,
    ) {
        let mut content_span = span.end.clone()..span.end.clone();
        let mut buffer = None;

        loop {
            let Some(ch) = interface.input().look_ahead() else {
                interface.error(
                    span.clone(),
                    Some(ErrorKind::SyntaxError),
                    format!("unterminated string"),
                );
                self.prev = '\0';
                break;
            };

            if ch.is_ascii_control() && *ch != '\t' {
                drop(ch);
                interface.error(
                    span.clone(),
                    Some(ErrorKind::SyntaxError),
                    format!("unterminated string"),
                );
                break;
            }

            let ch = ch.consume();
            span.end = ch.span().end;

            if *ch == quote {
                self.prev = *ch;
                break;
            }

            if *ch == '\\' {
                if buffer.is_none() {
                    buffer = Some(
                        interface
                            .input()
                            .span_str(content_span.clone())
                            .into_owned(),
                    );
                }
                content_span.end = span.end.clone();
                let buffer = buffer.as_mut().unwrap();
                let mut read_next_char =
                    |interface: &mut IF, prev: Option<&WithSpan<char, IF::Pos>>| {
                        let next = interface.input().look_ahead()?;
                        if next.is_ascii_control() && *next != '\t' {
                            return None;
                        }
                        if let Some(prev) = prev {
                            if *next == quote {
                                drop(next);
                                interface.error(
                                    &ch..prev,
                                    Some(ErrorKind::SyntaxError),
                                    format!("invalid escape sequence"),
                                );
                                return None;
                            }
                        }
                        let next = next.consume();
                        span.end = next.span().end;
                        content_span.end = span.end.clone();
                        Some(next)
                    };
                let mut check_hex_digit =
                    |interface: &mut IF, next: Option<WithSpan<char, IF::Pos>>, braced: bool| {
                        let next = next?;
                        if next.is_ascii_hexdigit() {
                            Some(next)
                        } else if braced && *next == '}' {
                            interface.error(
                                &ch..&next,
                                Some(ErrorKind::SyntaxError),
                                format!("invalid escape sequence: expected hexadecimal number"),
                            );
                            None
                        } else {
                            interface.error(
                                &ch..&next,
                                Some(ErrorKind::SyntaxError),
                                format!("invalid escape sequence: expected hexadecimal digit"),
                            );
                            buffer.push(*next);
                            None
                        }
                    };
                let Some(ch2) = read_next_char(interface, None) else {
                    continue;
                };
                match *ch2 {
                    '0' => buffer.push('\0'),
                    'n' => buffer.push('\n'),
                    'r' => buffer.push('\r'),
                    't' => buffer.push('\t'),
                    '\\' | '\'' | '"' => buffer.push(*ch2),
                    'x' => {
                        let hex1 = read_next_char(interface, Some(&ch2));
                        let Some(hex1) = check_hex_digit(interface, hex1, false) else {
                            continue;
                        };
                        let hex2 = read_next_char(interface, Some(&hex1));
                        let Some(hex2) = check_hex_digit(interface, hex2, false) else {
                            continue;
                        };
                        let code =
                            ((hex1.to_digit(16).unwrap() << 4) | hex2.to_digit(16).unwrap()) as u8;
                        buffer.push(code as char);
                    }
                    'u' => {
                        let Some(ch3) = read_next_char(interface, Some(&ch2)) else {
                            continue;
                        };
                        if *ch3 == '{' {
                            let hex1 = read_next_char(interface, Some(&ch3));
                            let Some(hex1) = check_hex_digit(interface, hex1, true) else {
                                continue;
                            };
                            let mut hex_span = hex1.span();
                            let mut prev = hex1;
                            while let Some(next) = read_next_char(interface, Some(&prev)) {
                                if *next == '}' {
                                    let hex = interface.input().span_str(hex_span.clone());
                                    if let Ok(code) = u32::from_str_radix(&hex, 16) {
                                        if let Some(ch) = char::from_u32(code) {
                                            buffer.push(ch);
                                            break;
                                        }
                                    }
                                    interface.error(
                                        hex_span,
                                        Some(ErrorKind::SyntaxError),
                                        format!("`{hex}` is not a valid Unicode character code"),
                                    );
                                    break;
                                } else if next.is_ascii_hexdigit() {
                                    hex_span.end = next.span().end;
                                } else {
                                    interface.error(
                                        &ch..&next,
                                        Some(ErrorKind::SyntaxError),
                                        format!("invalid escape sequence: expected hexadecimal digit or `}}`"),
                                    );
                                    buffer.push(*next);
                                    break;
                                }
                                prev = next;
                            }
                        } else {
                            interface.error(
                                &ch..&ch3,
                                Some(ErrorKind::SyntaxError),
                                format!("invalid escape sequence: expected `{{` after `\\u`"),
                            );
                            buffer.push(*ch3);
                        }
                    }
                    _ => {
                        interface.error(
                            &ch..&ch2,
                            Some(ErrorKind::SyntaxError),
                            format!("invalid escape sequence"),
                        );
                        buffer.push(*ch2);
                    }
                }
                continue;
            }

            content_span.end = span.end.clone();

            if let Some(buffer) = &mut buffer {
                buffer.push(*ch);
            }
        }

        let content = if let Some(buffer) = buffer {
            Cow::Owned(buffer)
        } else {
            interface.input().span_str(content_span)
        };
        let token = if is_quoted_identifier {
            Token::Ident(content, IdentifierType::Quoted)
        } else {
            Token::String(quote, content)
        };
        interface.out(span.clone(), token);
        if !is_quoted_identifier {
            interface.span_desc(span, SpanDesc::String);
        }
        self.dot_seen = false;
        self.dots_seen = false;
        self.dot_number_allowed = false;
    }
}

#[derive(Clone)]
pub struct TokenizerConfig;

impl CharParserDesc for TokenizerConfig {
    type Out<'a, Pos: Position> = Token<'a>;
    type Config<'a> = Self;

    type Parser<
        'a,
        Pos: Position,
        IF: ParserInterface<
            Config = Self::Config<'a>,
            In = char,
            Out = Self::Out<'a, Pos>,
            Pos = Pos,
            Input: CharParserInput<'a>,
        >,
    > = Tokenizer;

    fn parser<
        'a,
        Pos: Position,
        IF: ParserInterface<
            Config = Self::Config<'a>,
            In = char,
            Out = Self::Out<'a, Pos>,
            Pos = Pos,
            Input: CharParserInput<'a>,
        >,
    >(
        _interface: &IF,
    ) -> Self::Parser<'a, Pos, IF> {
        Tokenizer::new()
    }
}

#[derive(Clone, Copy, PartialEq, MemSerializable, Debug)]
pub enum TokenIsolation {
    Isolated,          // preceded/followed by whitespace
    WeaklyConnected,   // preceded/followed by punctuation or similar
    StronglyConnected, // preceded/followed by identifier or similar
}

impl TokenIsolation {
    fn get_pre_isolation(ch: char, prev: char) -> Self {
        if prev == '\0' || prev.is_whitespace() {
            TokenIsolation::Isolated
        } else if is_pre_weakly_connecting_char(prev) || prev == ch {
            TokenIsolation::WeaklyConnected
        } else {
            TokenIsolation::StronglyConnected
        }
    }

    fn get_post_isolation(ch: char, next: char) -> Self {
        if next == '\0' || next.is_whitespace() {
            TokenIsolation::Isolated
        } else if is_post_weakly_connecting_char(next) || next == ch {
            TokenIsolation::WeaklyConnected
        } else {
            TokenIsolation::StronglyConnected
        }
    }
}

#[derive(Clone, Copy, PartialEq, MemSerializable, Debug)]
pub enum IdentifierType {
    Unquoted,
    Quoted,
}

#[derive(Clone, PartialEq)]
enum IdentifierContent {
    // TODO: We probably want to distinguish between different classes of alphanumeric content, so
    //       that things like `λa` are two separate tokens.
    Alphanumeric,
    Symbol,
    Subscript,
    Superscript,
}

impl IdentifierContent {
    fn get(ch: char) -> Self {
        if is_symbol_char(ch) {
            IdentifierContent::Symbol
        } else if is_subscript_char(ch) {
            IdentifierContent::Subscript
        } else if is_superscript_char(ch) {
            IdentifierContent::Superscript
        } else {
            IdentifierContent::Alphanumeric
        }
    }
}

#[cfg(test)]
mod tests {
    use lang_test::parser::*;

    use super::*;

    fn assert_tokenizer_output(expected_fragments: Vec<ExpectedFragment<Token>>) {
        assert_parser_output::<TokenizerConfig>(expected_fragments, TokenizerConfig)
    }

    fn blank(input: &str) -> ExpectedFragment<Token> {
        (ExpectedFragmentContent::Input(input), None)
    }

    fn block_comment(content: ExpectedFragmentContent) -> ExpectedFragment<Token> {
        (
            ExpectedFragmentContent::WithDesc(
                Box::new(block_comment_content(content)),
                SpanDesc::Comment,
            ),
            None,
        )
    }

    fn block_comment_content(content: ExpectedFragmentContent) -> ExpectedFragmentContent {
        ExpectedFragmentContent::Seq(vec![
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Input("/*")),
                SpanDesc::ParenStart,
            ),
            content,
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Input("*/")),
                SpanDesc::ParenEnd,
            ),
        ])
    }

    fn unterminated_block_comment(content: ExpectedFragmentContent) -> ExpectedFragment<Token> {
        (
            ExpectedFragmentContent::WithDiag(
                Box::new(ExpectedFragmentContent::WithDesc(
                    Box::new(unterminated_block_comment_content(content)),
                    SpanDesc::Comment,
                )),
                (
                    DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                    "unterminated comment".into(),
                ),
            ),
            None,
        )
    }

    fn unterminated_block_comment_content(
        content: ExpectedFragmentContent,
    ) -> ExpectedFragmentContent {
        ExpectedFragmentContent::Seq(vec![
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Input("/*")),
                SpanDesc::ParenStart,
            ),
            content,
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Empty),
                SpanDesc::ParenEnd,
            ),
        ])
    }

    fn line_comment(content: ExpectedFragmentContent) -> ExpectedFragment<Token> {
        (
            ExpectedFragmentContent::WithDesc(
                Box::new(line_comment_content(content)),
                SpanDesc::Comment,
            ),
            None,
        )
    }

    fn line_comment_content(content: ExpectedFragmentContent) -> ExpectedFragmentContent {
        ExpectedFragmentContent::Seq(vec![ExpectedFragmentContent::Input("//"), content])
    }

    fn reserved_char(
        input: &str,
        pre_isolation: TokenIsolation,
        post_isolation: TokenIsolation,
    ) -> ExpectedFragment<Token> {
        let mut iter = input.chars();
        let ch = iter.next().unwrap();
        assert!(iter.next().is_none());
        (
            ExpectedFragmentContent::Input(input),
            Some(Token::ReservedChar(ch, pre_isolation, post_isolation)),
        )
    }

    fn keyword(keyword: &str) -> ExpectedFragment<Token> {
        (
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Input(keyword)),
                SpanDesc::Keyword,
            ),
            Some(Token::Keyword(keyword.into())),
        )
    }

    fn number(number: &str) -> ExpectedFragment<Token> {
        (
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Input(number)),
                SpanDesc::Number,
            ),
            Some(Token::Number(number.into())),
        )
    }

    fn unquoted_identifier(name: &str) -> ExpectedFragment<Token> {
        (
            ExpectedFragmentContent::Input(name),
            Some(Token::Ident(name.into(), IdentifierType::Unquoted)),
        )
    }

    fn quoted_identifier<'a>(input: &'a str, name: &'a str) -> ExpectedFragment<'a, Token<'a>> {
        (
            ExpectedFragmentContent::Input(input),
            Some(Token::Ident(name.into(), IdentifierType::Quoted)),
        )
    }

    fn string<'a>(input: &'a str, content: &'a str) -> ExpectedFragment<'a, Token<'a>> {
        (
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Input(input)),
                SpanDesc::String,
            ),
            Some(Token::String(input.chars().next().unwrap(), content.into())),
        )
    }

    #[test]
    fn whitespace() {
        assert_tokenizer_output(Vec::new());
        assert_tokenizer_output(vec![blank(" ")]);
        assert_tokenizer_output(vec![blank("\t")]);
        assert_tokenizer_output(vec![blank(" \n\t\r\n ")]);
        assert_tokenizer_output(vec![block_comment(ExpectedFragmentContent::Empty)]);
        assert_tokenizer_output(vec![block_comment(ExpectedFragmentContent::Input(" "))]);
        assert_tokenizer_output(vec![
            blank(" "),
            block_comment(ExpectedFragmentContent::Input(" ")),
            blank(" "),
        ]);
        assert_tokenizer_output(vec![block_comment(ExpectedFragmentContent::Input("*"))]);
        assert_tokenizer_output(vec![block_comment(ExpectedFragmentContent::Input(" // "))]);
        assert_tokenizer_output(vec![block_comment(block_comment_content(
            ExpectedFragmentContent::Empty,
        ))]);
        assert_tokenizer_output(vec![block_comment(block_comment_content(
            ExpectedFragmentContent::Input(" "),
        ))]);
        assert_tokenizer_output(vec![block_comment(ExpectedFragmentContent::Seq(vec![
            ExpectedFragmentContent::Input(" "),
            block_comment_content(ExpectedFragmentContent::Input(" ")),
            ExpectedFragmentContent::Input(" "),
        ]))]);
        assert_tokenizer_output(vec![
            blank(" "),
            block_comment(ExpectedFragmentContent::Input(" abc \n def ")),
            blank(" "),
            block_comment(ExpectedFragmentContent::Input(" ghi ")),
            blank(" "),
        ]);
        assert_tokenizer_output(vec![
            block_comment(ExpectedFragmentContent::Empty),
            unquoted_identifier("*/"),
        ]);
        assert_tokenizer_output(vec![unterminated_block_comment(
            ExpectedFragmentContent::Empty,
        )]);
        assert_tokenizer_output(vec![unterminated_block_comment(
            ExpectedFragmentContent::Input("/"),
        )]);
        assert_tokenizer_output(vec![unterminated_block_comment(
            ExpectedFragmentContent::Input("/ "),
        )]);
        assert_tokenizer_output(vec![unterminated_block_comment(block_comment_content(
            ExpectedFragmentContent::Empty,
        ))]);
        assert_tokenizer_output(vec![unterminated_block_comment(
            unterminated_block_comment_content(ExpectedFragmentContent::Input("/")),
        )]);
        assert_tokenizer_output(vec![unterminated_block_comment(
            ExpectedFragmentContent::Seq(vec![
                ExpectedFragmentContent::Input("/"),
                unterminated_block_comment_content(ExpectedFragmentContent::Input("/")),
            ]),
        )]);
        assert_tokenizer_output(vec![line_comment(ExpectedFragmentContent::Empty)]);
        assert_tokenizer_output(vec![line_comment(ExpectedFragmentContent::Input("/"))]);
        assert_tokenizer_output(vec![line_comment(ExpectedFragmentContent::Input(" "))]);
        assert_tokenizer_output(vec![
            line_comment(ExpectedFragmentContent::Empty),
            blank("\n"),
        ]);
        assert_tokenizer_output(vec![
            line_comment(ExpectedFragmentContent::Input(" ")),
            blank("\n"),
        ]);
    }

    #[test]
    fn reserved_chars() {
        assert_tokenizer_output(vec![reserved_char(
            ".",
            TokenIsolation::Isolated,
            TokenIsolation::Isolated,
        )]);
        assert_tokenizer_output(vec![
            blank(" "),
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
            blank(" "),
        ]);
        assert_tokenizer_output(vec![
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
            blank(" "),
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
        ]);
        assert_tokenizer_output(vec![
            blank(" "),
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
            blank(" "),
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
            blank(" "),
        ]);
        assert_tokenizer_output(vec![
            reserved_char(
                ".",
                TokenIsolation::Isolated,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::Isolated,
            ),
        ]);
        assert_tokenizer_output(vec![
            reserved_char(
                ".",
                TokenIsolation::Isolated,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::Isolated,
            ),
        ]);
        assert_tokenizer_output(vec![
            blank(" "),
            block_comment(ExpectedFragmentContent::Empty),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            block_comment(ExpectedFragmentContent::Empty),
            blank(" "),
        ]);
        assert_tokenizer_output(vec![
            blank(" "),
            block_comment(ExpectedFragmentContent::Empty),
            blank(" "),
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
            blank(" "),
            block_comment(ExpectedFragmentContent::Empty),
            blank(" "),
        ]);
        assert_tokenizer_output(vec![
            line_comment(ExpectedFragmentContent::Empty),
            blank("\n"),
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
        ]);
        assert_tokenizer_output(vec![
            blank(" "),
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
            blank(" "),
            line_comment(ExpectedFragmentContent::Input(" : ")),
            (ExpectedFragmentContent::Input("\n "), None),
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
        ]);
        assert_tokenizer_output(vec![
            reserved_char(
                ".",
                TokenIsolation::Isolated,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ",",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ";",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::StronglyConnected,
            ),
            reserved_char(
                "(",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ")",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::StronglyConnected,
            ),
            reserved_char(
                "[",
                TokenIsolation::StronglyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                "]",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::StronglyConnected,
            ),
            reserved_char(
                "{",
                TokenIsolation::StronglyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                "}",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::StronglyConnected,
            ),
            reserved_char(
                "|",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            reserved_char(
                "〈",
                TokenIsolation::StronglyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                "〉",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::Isolated,
            ),
        ]);
        assert_tokenizer_output(vec![
            reserved_char(
                "|",
                TokenIsolation::Isolated,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                "|",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::Isolated,
            ),
        ]);
        assert_tokenizer_output(vec![reserved_char(
            "_",
            TokenIsolation::Isolated,
            TokenIsolation::Isolated,
        )]);
        assert_tokenizer_output(vec![
            reserved_char(
                "(",
                TokenIsolation::Isolated,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("+"),
            reserved_char(
                ")",
                TokenIsolation::StronglyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("0"),
        ]);
    }

    #[test]
    fn keywords() {
        assert_tokenizer_output(vec![keyword("%x")]);
        assert_tokenizer_output(vec![keyword("%for")]);
        assert_tokenizer_output(vec![keyword("%for'")]);
        assert_tokenizer_output(vec![keyword("%for\"")]);
        assert_tokenizer_output(vec![unquoted_identifier("%")]);
        assert_tokenizer_output(vec![unquoted_identifier("%+")]);
        assert_tokenizer_output(vec![unquoted_identifier("%%")]);
        assert_tokenizer_output(vec![blank(" "), keyword("%for"), blank(" ")]);
        assert_tokenizer_output(vec![
            unquoted_identifier("%"),
            blank(" "),
            unquoted_identifier("for"),
        ]);
        assert_tokenizer_output(vec![keyword("%for"), blank(" "), keyword("%each")]);
        assert_tokenizer_output(vec![
            keyword("%for"),
            blank(" "),
            unquoted_identifier("each"),
        ]);
        assert_tokenizer_output(vec![
            keyword("%for"),
            reserved_char(
                "_",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("each"),
        ]);
        assert_tokenizer_output(vec![
            keyword("%for"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("each"),
        ]);
        assert_tokenizer_output(vec![keyword("%for'"), unquoted_identifier("each")]);
    }

    #[test]
    fn identifiers() {
        assert_tokenizer_output(vec![unquoted_identifier("x")]);
        assert_tokenizer_output(vec![unquoted_identifier("+")]);
        assert_tokenizer_output(vec![unquoted_identifier("xyz")]);
        assert_tokenizer_output(vec![unquoted_identifier("+-")]);
        assert_tokenizer_output(vec![unquoted_identifier("a1")]);
        assert_tokenizer_output(vec![unquoted_identifier("a'")]);
        assert_tokenizer_output(vec![unquoted_identifier("a\"")]);
        assert_tokenizer_output(vec![unquoted_identifier("a''")]);
        assert_tokenizer_output(vec![unquoted_identifier("+/*")]);
        assert_tokenizer_output(vec![
            unquoted_identifier("x"),
            blank(" "),
            unquoted_identifier("y"),
            blank(" "),
            unquoted_identifier("z"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("x"),
            blank(" "),
            unquoted_identifier("+"),
            blank(" "),
            unquoted_identifier("y"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("x"),
            unquoted_identifier("+"),
            unquoted_identifier("y"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("xy"),
            unquoted_identifier("+="),
            unquoted_identifier("z"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("x"),
            blank(" "),
            string("'*'", "*"),
            blank(" "),
            unquoted_identifier("y\""),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("x'"),
            unquoted_identifier("*'"),
            unquoted_identifier("y\""),
        ]);
        assert_tokenizer_output(vec![unquoted_identifier("a'"), unquoted_identifier("b")]);
        assert_tokenizer_output(vec![unquoted_identifier("a'"), unquoted_identifier("+")]);
        assert_tokenizer_output(vec![
            unquoted_identifier("a"),
            reserved_char(
                "_",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("b"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("a"),
            reserved_char(
                "_",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("+"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("+"),
            reserved_char(
                "_",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("a"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("a"),
            reserved_char(
                "_",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            number("1"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("a"),
            reserved_char(
                "^",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            number("2"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("a"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("b"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("a"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("b"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("a"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("b"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("-"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("-"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("ℕ"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("0"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("ℕ"),
            blank(" "),
            reserved_char(
                ".",
                TokenIsolation::Isolated,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("0"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("f"),
            reserved_char(
                "(",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("x"),
            reserved_char(
                ")",
                TokenIsolation::StronglyConnected,
                TokenIsolation::Isolated,
            ),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("f"),
            reserved_char(
                "(",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("-"),
            reserved_char(
                ")",
                TokenIsolation::StronglyConnected,
                TokenIsolation::Isolated,
            ),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("f"),
            reserved_char(
                "(",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("xy"),
            reserved_char(
                ",",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("-"),
            reserved_char(
                ")",
                TokenIsolation::StronglyConnected,
                TokenIsolation::Isolated,
            ),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("x"),
            blank(" "),
            quoted_identifier("@\".\"", "."),
            blank(" "),
            unquoted_identifier("y"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("x"),
            quoted_identifier("@\".\"", "."),
            unquoted_identifier("y"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("x"),
            unquoted_identifier("@"),
            unquoted_identifier("y"),
        ]);
        assert_tokenizer_output(vec![quoted_identifier("@\"x+y.z\"", "x+y.z")]);
        assert_tokenizer_output(vec![quoted_identifier("@\"\"", "")]);
        assert_tokenizer_output(vec![quoted_identifier("@\"\\n\"", "\n")]);
        assert_tokenizer_output(vec![
            unquoted_identifier("abc"),
            blank(" "),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Input("@\"def")),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unterminated string".into(),
                    ),
                ),
                Some(Token::Ident("def".into(), IdentifierType::Quoted)),
            ),
        ]);
    }

    #[test]
    fn sub_and_superscripts() {
        assert_tokenizer_output(vec![unquoted_identifier("a"), unquoted_identifier("ₙ")]);
        assert_tokenizer_output(vec![unquoted_identifier("a'"), unquoted_identifier("ₙ")]);
        assert_tokenizer_output(vec![unquoted_identifier("+"), unquoted_identifier("ₙ")]);
        assert_tokenizer_output(vec![unquoted_identifier("a"), unquoted_identifier("²")]);
        assert_tokenizer_output(vec![unquoted_identifier("a'"), unquoted_identifier("²")]);
        assert_tokenizer_output(vec![unquoted_identifier("+"), unquoted_identifier("²")]);
        assert_tokenizer_output(vec![unquoted_identifier("a"), unquoted_identifier("⁻¹")]);
        assert_tokenizer_output(vec![unquoted_identifier("+"), unquoted_identifier("⁻¹")]);
        assert_tokenizer_output(vec![
            unquoted_identifier("a"),
            unquoted_identifier("ₙ"),
            unquoted_identifier("⁻¹"),
        ]);
    }

    #[test]
    fn numbers() {
        assert_tokenizer_output(vec![number("0")]);
        assert_tokenizer_output(vec![number("123")]);
        assert_tokenizer_output(vec![number("12.345")]);
        assert_tokenizer_output(vec![number("12.")]);
        assert_tokenizer_output(vec![number(".345")]);
        assert_tokenizer_output(vec![number("1_234_567.89")]);
        assert_tokenizer_output(vec![number("12.34e5")]);
        assert_tokenizer_output(vec![number("12.34e+56")]);
        assert_tokenizer_output(vec![number("12.3e-456")]);
        assert_tokenizer_output(vec![number(".3e-456")]);
        assert_tokenizer_output(vec![number("0xf00")]);
        assert_tokenizer_output(vec![number("0xf00.ba1")]);
        assert_tokenizer_output(vec![number("1_foo.bar")]);
        assert_tokenizer_output(vec![
            blank(" "),
            number("0"),
            blank(" "),
            number("1"),
            blank(" "),
            number(".2"),
            blank(" "),
            number("3."),
            blank(" "),
            number("4"),
            blank(" "),
        ]);
        assert_tokenizer_output(vec![
            blank(" "),
            number("0"),
            blank(" "),
            number("1"),
            blank(" "),
            reserved_char(".", TokenIsolation::Isolated, TokenIsolation::Isolated),
            blank(" "),
            unquoted_identifier("2"),
            blank(" "),
            number("3.4"),
            blank(" "),
        ]);
        assert_tokenizer_output(vec![
            blank(" "),
            number("0.1"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("2"),
        ]);
        assert_tokenizer_output(vec![
            blank(" "),
            number("0"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::StronglyConnected,
            ),
            number("1"),
        ]);
        assert_tokenizer_output(vec![
            blank(" "),
            number("0"),
            blank(" "),
            reserved_char(
                ".",
                TokenIsolation::Isolated,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::Isolated,
            ),
            blank(" "),
            number("1"),
        ]);
        assert_tokenizer_output(vec![number("0."), blank(" "), number(".1")]);
        assert_tokenizer_output(vec![
            blank(" "),
            number("0"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::StronglyConnected,
            ),
            number("1"),
            reserved_char(
                ".",
                TokenIsolation::StronglyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::WeaklyConnected,
            ),
            reserved_char(
                ".",
                TokenIsolation::WeaklyConnected,
                TokenIsolation::StronglyConnected,
            ),
            unquoted_identifier("n"),
        ]);
        assert_tokenizer_output(vec![
            number("1"),
            unquoted_identifier("+"),
            number("2.3e4"),
            unquoted_identifier("-"),
            number("5"),
        ]);
        assert_tokenizer_output(vec![number(".1"), unquoted_identifier("+"), number(".2")]);
        assert_tokenizer_output(vec![
            reserved_char(
                "(",
                TokenIsolation::Isolated,
                TokenIsolation::WeaklyConnected,
            ),
            number(".1"),
            blank(" "),
            number(".2"),
            reserved_char(
                ")",
                TokenIsolation::StronglyConnected,
                TokenIsolation::Isolated,
            ),
        ]);
    }

    #[test]
    fn strings() {
        assert_tokenizer_output(vec![string("''", "")]);
        assert_tokenizer_output(vec![string("'abc'", "abc")]);
        assert_tokenizer_output(vec![string("'\"'", "\"")]);
        assert_tokenizer_output(vec![string("'/*'", "/*")]);
        assert_tokenizer_output(vec![string("\"\"", "")]);
        assert_tokenizer_output(vec![string("\"abc\"", "abc")]);
        assert_tokenizer_output(vec![string("\"'\"", "'")]);
        assert_tokenizer_output(vec![string("\"/*\"", "/*")]);
        assert_tokenizer_output(vec![string("'abc'", "abc"), string("\"abc\"", "abc")]);
        assert_tokenizer_output(vec![string("\"abc\"", "abc"), string("\"abc\"", "abc")]);
        assert_tokenizer_output(vec![
            blank(" "),
            string("'abc'", "abc"),
            blank(" "),
            string("\"abc\"", "abc"),
            blank(" "),
        ]);
        assert_tokenizer_output(vec![string("\"abc /*def*/ ghi\"", "abc /*def*/ ghi")]);
        assert_tokenizer_output(vec![string("'\\n'", "\n")]);
        assert_tokenizer_output(vec![string("'\\\''", "'")]);
        assert_tokenizer_output(vec![string("'\\\\'", "\\")]);
        assert_tokenizer_output(vec![string("\"\\n\"", "\n")]);
        assert_tokenizer_output(vec![string("\"\\\"\"", "\"")]);
        assert_tokenizer_output(vec![string("\"\\\\\"", "\\")]);
        assert_tokenizer_output(vec![string("\"abc\\ndef\"", "abc\ndef")]);
        assert_tokenizer_output(vec![string("\"abc\\r\\n\\tdef\\0\"", "abc\r\n\tdef\0")]);
        assert_tokenizer_output(vec![string("\"\\x17\"", "\x17")]);
        assert_tokenizer_output(vec![string("\"\\x0c\"", "\x0c")]);
        assert_tokenizer_output(vec![string("\"abc\\x17def\"", "abc\x17def")]);
        assert_tokenizer_output(vec![string("\"\\u{17}\"", "\u{17}")]);
        assert_tokenizer_output(vec![string("\"abc\\u{17}def\"", "abc\u{17}def")]);
        assert_tokenizer_output(vec![(
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Seq(vec![
                    ExpectedFragmentContent::Input("\""),
                    ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\\u4")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "invalid escape sequence: expected `{` after `\\u`".into(),
                        ),
                    ),
                    ExpectedFragmentContent::Input("2\""),
                ])),
                SpanDesc::String,
            ),
            Some(Token::String('"', "42".into())),
        )]);
        assert_tokenizer_output(vec![(
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Seq(vec![
                    ExpectedFragmentContent::Input("\""),
                    ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\\u{}")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "invalid escape sequence: expected hexadecimal number".into(),
                        ),
                    ),
                    ExpectedFragmentContent::Input("\""),
                ])),
                SpanDesc::String,
            ),
            Some(Token::String('"', "".into())),
        )]);
        assert_tokenizer_output(vec![string("\"\\u{e3a}\"", "\u{e3a}")]);
        assert_tokenizer_output(vec![(
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Seq(vec![
                    ExpectedFragmentContent::Input("\""),
                    ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\\u{e3g")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "invalid escape sequence: expected hexadecimal digit or `}`".into(),
                        ),
                    ),
                    ExpectedFragmentContent::Input("}\""),
                ])),
                SpanDesc::String,
            ),
            Some(Token::String('"', "g}".into())),
        )]);
        assert_tokenizer_output(vec![(
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Seq(vec![
                    ExpectedFragmentContent::Input("\""),
                    ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\\u{e3a")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "invalid escape sequence".into(),
                        ),
                    ),
                    ExpectedFragmentContent::Input("\""),
                ])),
                SpanDesc::String,
            ),
            Some(Token::String('"', "".into())),
        )]);
        assert_tokenizer_output(vec![(
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Seq(vec![
                    ExpectedFragmentContent::Input("\""),
                    ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\\u{e3g")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "invalid escape sequence: expected hexadecimal digit or `}`".into(),
                        ),
                    ),
                    ExpectedFragmentContent::Input("\""),
                ])),
                SpanDesc::String,
            ),
            Some(Token::String('"', "g".into())),
        )]);
        assert_tokenizer_output(vec![(
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Seq(vec![
                    ExpectedFragmentContent::Input("\"\\u{"),
                    ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("d800")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "`d800` is not a valid Unicode character code".into(),
                        ),
                    ),
                    ExpectedFragmentContent::Input("}\""),
                ])),
                SpanDesc::String,
            ),
            Some(Token::String('"', "".into())),
        )]);
        assert_tokenizer_output(vec![string("\"\\u{10000}\"", "\u{10000}")]);
        assert_tokenizer_output(vec![(
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Seq(vec![
                    ExpectedFragmentContent::Input("\"abc\\u{"),
                    ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("10000000")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "`10000000` is not a valid Unicode character code".into(),
                        ),
                    ),
                    ExpectedFragmentContent::Input("}def\""),
                ])),
                SpanDesc::String,
            ),
            Some(Token::String('"', "abcdef".into())),
        )]);
        assert_tokenizer_output(vec![(
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::Seq(vec![
                    ExpectedFragmentContent::Input("\"a"),
                    ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\\b")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "invalid escape sequence".into(),
                        ),
                    ),
                    ExpectedFragmentContent::Input("c\""),
                ])),
                SpanDesc::String,
            ),
            Some(Token::String('"', "abc".into())),
        )]);
        assert_tokenizer_output(vec![(
            ExpectedFragmentContent::WithDesc(
                Box::new(ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Input("\"")),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unterminated string".into(),
                    ),
                )),
                SpanDesc::String,
            ),
            Some(Token::String('"', "".into())),
        )]);
        assert_tokenizer_output(vec![
            blank(" "),
            unquoted_identifier("abc"),
            blank(" "),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\" def ")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "unterminated string".into(),
                        ),
                    )),
                    SpanDesc::String,
                ),
                Some(Token::String('"', " def ".into())),
            ),
        ]);
        assert_tokenizer_output(vec![
            blank(" "),
            unquoted_identifier("abc"),
            blank(" "),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\" def \\")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "unterminated string".into(),
                        ),
                    )),
                    SpanDesc::String,
                ),
                Some(Token::String('"', " def ".into())),
            ),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("abc"),
            blank(" "),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\"def")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "unterminated string".into(),
                        ),
                    )),
                    SpanDesc::String,
                ),
                Some(Token::String('"', "def".into())),
            ),
            blank("\n"),
            unquoted_identifier("ghi"),
        ]);
        assert_tokenizer_output(vec![
            unquoted_identifier("abc"),
            blank(" "),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::WithDiag(
                        Box::new(ExpectedFragmentContent::Input("\"def\\")),
                        (
                            DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                            "unterminated string".into(),
                        ),
                    )),
                    SpanDesc::String,
                ),
                Some(Token::String('"', "def".into())),
            ),
            blank("\n"),
            unquoted_identifier("ghi"),
        ]);
    }
}
