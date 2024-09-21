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
    use lang_def::parser::{DiagnosticSeverity::*, ErrorKind::*};
    use lang_test::parser::{ExpectedFragmentContent::*, *};

    use super::{IdentifierType::*, Token::*, TokenEvent::*, *};

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
            Input("abc"),
            Some(Token(Ident("abc".into(), Unquoted))),
        )]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("abc"), Some(Token(Ident("abc".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (Input("abc"), Some(Token(Ident("abc".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (Input("abc"), Some(Token(Ident("abc".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("abc"), Some(Token(Ident("abc".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("abc"), Some(Token(Ident("abc".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (
                WithDesc(Box::new(Input("%abc")), SpanDesc::Keyword),
                Some(Token(Keyword("%abc".into()))),
            ),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (
                Input("^"),
                Some(Token(ReservedChar(
                    '^',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ))),
            ),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input("⁻¹"), Some(Token(Ident("⁻¹".into(), Unquoted)))),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input("²"), Some(Token(Ident("²".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input("⁻¹"), Some(Token(Ident("⁻¹".into(), Unquoted)))),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input("+"), Some(Token(Ident("+".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
            (Input("-"), Some(Token(Ident("-".into(), Unquoted)))),
            (Input("c"), Some(Token(Ident("c".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input("⁻¹"), Some(Token(Ident("⁻¹".into(), Unquoted)))),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                Input("|"),
                Some(Token(ReservedChar(
                    '|',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ))),
            ),
            (
                Input("|"),
                Some(Token(ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (
                Input("|"),
                Some(Token(ReservedChar(
                    '|',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                ))),
            ),
            (
                Input("|"),
                Some(Token(ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                ))),
            ),
            (
                Input("|"),
                Some(Token(ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                ))),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
            (Input(" "), None),
            (Input("c"), Some(Token(Ident("c".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                Some(ParenStart('[')),
            ),
            (Input("d"), Some(Token(Ident("d".into(), Unquoted)))),
            (
                Input("|"),
                Some(Token(ReservedChar(
                    '|',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ))),
            ),
            (Input("e"), Some(Token(Ident("e".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input(" "), None),
            (Input("f"), Some(Token(Ident("f".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("⟦")), SpanDesc::ParenStart),
                Some(ParenStart('⟦')),
            ),
            (Input("g"), Some(Token(Ident("g".into(), Unquoted)))),
            (Input(" "), None),
            (
                Input("‖"),
                Some(Token(ReservedChar(
                    '‖',
                    TokenIsolation::Isolated,
                    TokenIsolation::Isolated,
                ))),
            ),
            (Input(" "), None),
            (Input("h"), Some(Token(Ident("h".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("⟧")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("‖")), SpanDesc::ParenStart),
                Some(ParenStart('‖')),
            ),
            (Input("i"), Some(Token(Ident("i".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("‖")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (
                Input("."),
                Some(Token(ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                ))),
            ),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (Input("j"), Some(Token(Ident("j".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
        ]);
    }

    #[test]
    fn unmatched_parentheses() {
        assert_parenthesis_matcher_output(vec![
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Empty), SpanDesc::ParenEnd)),
                    (
                        Error(Some(SyntaxError)),
                        "unmatched parenthesis: `)` expected".into(),
                    ),
                ),
                Some(ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![(
            WithDiag(
                Box::new(Input(")")),
                (Error(Some(SyntaxError)), "unmatched parenthesis".into()),
            ),
            None,
        )]);
        assert_parenthesis_matcher_output(vec![
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
            (Input(" "), None),
            (Input("c"), Some(Token(Ident("c".into(), Unquoted)))),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Empty), SpanDesc::ParenEnd)),
                    (
                        Error(Some(SyntaxError)),
                        "unmatched parenthesis: `)` expected".into(),
                    ),
                ),
                Some(ParenEnd),
            ),
        ]);
        assert_parenthesis_matcher_output(vec![
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input(" "), None),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
            (
                WithDiag(
                    Box::new(Input(")")),
                    (Error(Some(SyntaxError)), "unmatched parenthesis".into()),
                ),
                None,
            ),
            (Input(" "), None),
            (Input("c"), Some(Token(Ident("c".into(), Unquoted)))),
        ]);
        assert_parenthesis_matcher_output(vec![
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                Some(ParenStart('[')),
            ),
            (Input("c"), Some(Token(Ident("c".into(), Unquoted)))),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Empty), SpanDesc::ParenEnd)),
                    (
                        Error(Some(SyntaxError)),
                        "unmatched parenthesis: `]` expected".into(),
                    ),
                ),
                Some(ParenEnd),
            ),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input(" "), None),
            (Input("d"), Some(Token(Ident("d".into(), Unquoted)))),
        ]);
        assert_parenthesis_matcher_output(vec![
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                Some(ParenStart('|')),
            ),
            (Input("c"), Some(Token(Ident("c".into(), Unquoted)))),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Empty), SpanDesc::ParenEnd)),
                    (
                        Error(Some(SyntaxError)),
                        "unmatched parenthesis: `|` expected".into(),
                    ),
                ),
                Some(ParenEnd),
            ),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input(" "), None),
            (Input("d"), Some(Token(Ident("d".into(), Unquoted)))),
        ]);
        assert_parenthesis_matcher_output(vec![
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
            (
                WithDiag(
                    Box::new(Input("]")),
                    (Error(Some(SyntaxError)), "unmatched parenthesis".into()),
                ),
                None,
            ),
            (Input(" "), None),
            (Input("c"), Some(Token(Ident("c".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input(" "), None),
            (Input("d"), Some(Token(Ident("d".into(), Unquoted)))),
        ]);
        assert_parenthesis_matcher_output(vec![
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
            (
                WithDiag(
                    Box::new(Input("|")),
                    (Error(Some(SyntaxError)), "unmatched parenthesis".into()),
                ),
                None,
            ),
            (Input(" "), None),
            (Input("c"), Some(Token(Ident("c".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input(" "), None),
            (Input("d"), Some(Token(Ident("d".into(), Unquoted)))),
        ]);
        assert_parenthesis_matcher_output(vec![
            (Input("a"), Some(Token(Ident("a".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (Input("b"), Some(Token(Ident("b".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                Some(ParenStart('(')),
            ),
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParenStart('{')),
            ),
            (Input("c"), Some(Token(Ident("c".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                Some(ParenStart('[')),
            ),
            (Input("d"), Some(Token(Ident("d".into(), Unquoted)))),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                Some(ParenStart('[')),
            ),
            (Input("e"), Some(Token(Ident("e".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input(" "), None),
            (Input("f"), Some(Token(Ident("f".into(), Unquoted)))),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Empty), SpanDesc::ParenEnd)),
                    (
                        Error(Some(SyntaxError)),
                        "unmatched parenthesis: `]` expected".into(),
                    ),
                ),
                Some(ParenEnd),
            ),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Empty), SpanDesc::ParenEnd)),
                    (
                        Error(Some(SyntaxError)),
                        "unmatched parenthesis: `}` expected".into(),
                    ),
                ),
                Some(ParenEnd),
            ),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input(" "), None),
            (Input("g"), Some(Token(Ident("g".into(), Unquoted)))),
            (
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                Some(ParenEnd),
            ),
            (Input(" "), None),
            (Input("h"), Some(Token(Ident("h".into(), Unquoted)))),
        ]);
    }
}
