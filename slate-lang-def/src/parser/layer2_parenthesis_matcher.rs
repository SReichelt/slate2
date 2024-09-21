use lang_def::{
    mem_serializable::*,
    parser::{compose::*, *},
};

use super::{chars::*, layer1_tokenizer::*};

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub enum TokenEvent<'a> {
    Token(Token<'a>),
    ParenStart(char),
    ParenEnd,
}

#[derive(MemSerializable)]
pub struct ParenthesisMatcher {
    expected_closing_parentheses: Vec<char>,
}

impl ParenthesisMatcher {
    pub fn new() -> Self {
        ParenthesisMatcher {
            expected_closing_parentheses: Vec::new(),
        }
    }
}

impl<'a, IF: ParserInterface<In = Token<'a>, Out = TokenEvent<'a>>> Parser<IF>
    for ParenthesisMatcher
{
    fn parse(&mut self, interface: &mut IF) -> bool {
        let input = interface.input();

        let Some(token) = input.next() else {
            let pos = interface.input().pos();
            self.close_unmatched_groups(interface, pos, 0);
            return true;
        };

        let span = token.span();

        if let Token::ReservedChar(ch, pre_isolation, post_isolation) = *token {
            let mut is_symmetric_paren = false;

            if let Some(expected_closing_parenthesis) = matching_closing_parenthesis(ch) {
                is_symmetric_paren = expected_closing_parenthesis == ch;
                if !is_symmetric_paren
                    || (pre_isolation != TokenIsolation::StronglyConnected
                        && post_isolation == TokenIsolation::StronglyConnected)
                {
                    self.expected_closing_parentheses
                        .push(expected_closing_parenthesis);
                    interface.out_with_desc(span, TokenEvent::ParenStart(ch), SpanDesc::ParenStart);
                    return false;
                }
            }

            if is_closing_parenthesis(ch)
                || (is_symmetric_paren
                    && pre_isolation == TokenIsolation::StronglyConnected
                    && post_isolation != TokenIsolation::StronglyConnected)
            {
                if let Some(closed_group_index) = self
                    .expected_closing_parentheses
                    .iter()
                    .rposition(|&expected| expected == ch)
                {
                    self.close_unmatched_groups(
                        interface,
                        span.start.clone(),
                        closed_group_index + 1,
                    );
                    self.expected_closing_parentheses.pop();
                    interface.out_with_desc(span, TokenEvent::ParenEnd, SpanDesc::ParenEnd);
                } else {
                    interface.error(
                        span,
                        Some(ErrorKind::SyntaxError),
                        format!("unmatched parenthesis"),
                    );
                }
                return false;
            }
        }

        interface.out(span, TokenEvent::Token(token.into_inner()));
        false
    }
}

impl ParenthesisMatcher {
    fn close_unmatched_groups<'a, IF: ParserInterface<In = Token<'a>, Out = TokenEvent<'a>>>(
        &mut self,
        interface: &mut IF,
        pos: IF::Pos,
        target_len: usize,
    ) {
        while self.expected_closing_parentheses.len() > target_len {
            let expected = self.expected_closing_parentheses.pop().unwrap();
            interface.error(
                pos.clone(),
                Some(ErrorKind::SyntaxError),
                format!("unmatched parenthesis: `{expected}` expected"),
            );
            interface.out_with_desc(pos.clone(), TokenEvent::ParenEnd, SpanDesc::ParenEnd);
        }
    }
}

#[derive(Clone)]
pub struct ParenthesisMatcherConfig;

impl CharParserDesc for ParenthesisMatcherConfig {
    type Out<'a, Pos: Position> = TokenEvent<'a>;
    type Config<'a> = (TokenizerConfig, Self);

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
    > = ComposedParser<IF, Token<'a>, Tokenizer, ParenthesisMatcher>;

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
        ComposedParser::new(Tokenizer::new(), ParenthesisMatcher::new())
    }
}

#[cfg(test)]
mod tests {
    use lang_test::parser::*;

    use super::*;

    fn assert_parenthesis_matcher_output(expected_fragments: Vec<ExpectedFragment<TokenEvent>>) {
        assert_parser_output::<ParenthesisMatcherConfig>(
            expected_fragments,
            (TokenizerConfig, ParenthesisMatcherConfig),
        )
    }

    #[test]
    fn matched_parentheses() {
        assert_parenthesis_matcher_output(vec![]);
        assert_parenthesis_matcher_output(vec![(
            ExpectedFragmentContent::Input("abc"),
            Some(TokenEvent::Token(Token::Ident(
                "abc".into(),
                IdentifierType::Unquoted,
            ))),
        )]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("abc"),
                Some(TokenEvent::Token(Token::Ident(
                    "abc".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::Input("abc"),
                Some(TokenEvent::Token(Token::Ident(
                    "abc".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::Input("abc"),
                Some(TokenEvent::Token(Token::Ident(
                    "abc".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("abc"),
                Some(TokenEvent::Token(Token::Ident(
                    "abc".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("abc"),
                Some(TokenEvent::Token(Token::Ident(
                    "abc".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%abc")),
                    SpanDesc::Keyword,
                ),
                Some(TokenEvent::Token(Token::Keyword("%abc".into()))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::Input("^"),
                Some(TokenEvent::Token(Token::ReservedChar(
                    '^',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::Input("⁻¹"),
                Some(TokenEvent::Token(Token::Ident(
                    "⁻¹".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("²"),
                Some(TokenEvent::Token(Token::Ident(
                    "²".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::Input("⁻¹"),
                Some(TokenEvent::Token(Token::Ident(
                    "⁻¹".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("+"),
                Some(TokenEvent::Token(Token::Ident(
                    "+".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("-"),
                Some(TokenEvent::Token(Token::Ident(
                    "-".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("c"),
                Some(TokenEvent::Token(Token::Ident(
                    "c".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::Input("⁻¹"),
                Some(TokenEvent::Token(Token::Ident(
                    "⁻¹".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("|"),
                Some(TokenEvent::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("|"),
                Some(TokenEvent::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("|"),
                Some(TokenEvent::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("|"),
                Some(TokenEvent::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("|"),
                Some(TokenEvent::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("c"),
                Some(TokenEvent::Token(Token::Ident(
                    "c".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("[")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('[')),
            ),
            (
                ExpectedFragmentContent::Input("d"),
                Some(TokenEvent::Token(Token::Ident(
                    "d".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("|"),
                Some(TokenEvent::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ))),
            ),
            (
                ExpectedFragmentContent::Input("e"),
                Some(TokenEvent::Token(Token::Ident(
                    "e".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("]")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("f"),
                Some(TokenEvent::Token(Token::Ident(
                    "f".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("⟦")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('⟦')),
            ),
            (
                ExpectedFragmentContent::Input("g"),
                Some(TokenEvent::Token(Token::Ident(
                    "g".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("‖"),
                Some(TokenEvent::Token(Token::ReservedChar(
                    '‖',
                    TokenIsolation::Isolated,
                    TokenIsolation::Isolated,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("h"),
                Some(TokenEvent::Token(Token::Ident(
                    "h".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("⟧")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("‖")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('‖')),
            ),
            (
                ExpectedFragmentContent::Input("i"),
                Some(TokenEvent::Token(Token::Ident(
                    "i".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("‖")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::Input("."),
                Some(TokenEvent::Token(Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::Input("j"),
                Some(TokenEvent::Token(Token::Ident(
                    "j".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
    }

    #[test]
    fn unmatched_parentheses() {
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Empty),
                        SpanDesc::ParenEnd,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unmatched parenthesis: `)` expected".into(),
                    ),
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![(
            ExpectedFragmentContent::WithDiag(
                Box::new(ExpectedFragmentContent::Input(")")),
                (
                    DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                    "unmatched parenthesis".into(),
                ),
            ),
            None,
        )]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("c"),
                Some(TokenEvent::Token(Token::Ident(
                    "c".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Empty),
                        SpanDesc::ParenEnd,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unmatched parenthesis: `)` expected".into(),
                    ),
                ),
                Some(TokenEvent::ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unmatched parenthesis".into(),
                    ),
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("c"),
                Some(TokenEvent::Token(Token::Ident(
                    "c".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("[")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('[')),
            ),
            (
                ExpectedFragmentContent::Input("c"),
                Some(TokenEvent::Token(Token::Ident(
                    "c".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Empty),
                        SpanDesc::ParenEnd,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unmatched parenthesis: `]` expected".into(),
                    ),
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("d"),
                Some(TokenEvent::Token(Token::Ident(
                    "d".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('|')),
            ),
            (
                ExpectedFragmentContent::Input("c"),
                Some(TokenEvent::Token(Token::Ident(
                    "c".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Empty),
                        SpanDesc::ParenEnd,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unmatched parenthesis: `|` expected".into(),
                    ),
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("d"),
                Some(TokenEvent::Token(Token::Ident(
                    "d".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Input("]")),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unmatched parenthesis".into(),
                    ),
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("c"),
                Some(TokenEvent::Token(Token::Ident(
                    "c".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("d"),
                Some(TokenEvent::Token(Token::Ident(
                    "d".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Input("|")),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unmatched parenthesis".into(),
                    ),
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("c"),
                Some(TokenEvent::Token(Token::Ident(
                    "c".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("d"),
                Some(TokenEvent::Token(Token::Ident(
                    "d".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                ExpectedFragmentContent::Input("a"),
                Some(TokenEvent::Token(Token::Ident(
                    "a".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::Input("b"),
                Some(TokenEvent::Token(Token::Ident(
                    "b".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("(")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('(')),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("{")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('{')),
            ),
            (
                ExpectedFragmentContent::Input("c"),
                Some(TokenEvent::Token(Token::Ident(
                    "c".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("[")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('[')),
            ),
            (
                ExpectedFragmentContent::Input("d"),
                Some(TokenEvent::Token(Token::Ident(
                    "d".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("[")),
                    SpanDesc::ParenStart,
                ),
                Some(TokenEvent::ParenStart('[')),
            ),
            (
                ExpectedFragmentContent::Input("e"),
                Some(TokenEvent::Token(Token::Ident(
                    "e".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("]")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("f"),
                Some(TokenEvent::Token(Token::Ident(
                    "f".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Empty),
                        SpanDesc::ParenEnd,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unmatched parenthesis: `]` expected".into(),
                    ),
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Empty),
                        SpanDesc::ParenEnd,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "unmatched parenthesis: `}` expected".into(),
                    ),
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("g"),
                Some(TokenEvent::Token(Token::Ident(
                    "g".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input(")")),
                    SpanDesc::ParenEnd,
                ),
                Some(TokenEvent::ParenEnd),
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("h"),
                Some(TokenEvent::Token(Token::Ident(
                    "h".into(),
                    IdentifierType::Unquoted,
                ))),
            ),
        ]);
    }
}
