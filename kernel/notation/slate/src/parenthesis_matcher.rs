use std::ops::Range;

use slate_kernel_notation_generic::{event::*, event_translator::*};

use crate::{chars::matching_closing_parenthesis, tokenizer::*};

// `TokenEvent` serializes `ParenToken` (defined in tests below) into events.
#[derive(Clone, PartialEq, Debug)]
pub enum TokenEvent<'a> {
    Token(Token<'a>),
    GroupStart(char),
    GroupEnd,
}

impl Event for TokenEvent<'_> {}

pub struct ParenthesisMatcher;

impl<'a> EventTranslator<'a> for ParenthesisMatcher {
    type In = Token<'a>;
    type Out = TokenEvent<'a>;
    type Pass<Src: EventSource + 'a> = ParenthesisMatcherPass<'a, Src>;

    fn start<Src: EventSource + 'a>(
        &self,
        source: EventSourceWithOps<'a, Self::In, Src>,
    ) -> Self::Pass<Src> {
        ParenthesisMatcherPass { source }
    }
}

pub struct ParenthesisMatcherPass<'a, Src: EventSource + 'a> {
    source: EventSourceWithOps<'a, Token<'a>, Src>,
}

impl<'a, Src: EventSource + 'a> EventTranslatorPass for ParenthesisMatcherPass<'a, Src> {
    type In = Token<'a>;
    type Out = TokenEvent<'a>;
    type Marker = Src::Marker;
    type State = ParenthesisMatcherState<Src::Marker>;

    fn new_state(&self) -> Self::State {
        Vec::new()
    }

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        range: Range<&Self::Marker>,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) {
        if let Token::ReservedChar(c) = event {
            if let Some(expected_closing_parenthesis) = matching_closing_parenthesis(c) {
                state.push(TokenGroupState {
                    group_start: range.start.clone(),
                    expected_closing_parenthesis,
                });
                out(TokenEvent::GroupStart(c), range);
                return;
            }

            if let Some(closed_group_index) = state
                .iter()
                .rposition(|group| group.expected_closing_parenthesis == c)
            {
                self.close_unmatched_groups(state, range.start, &mut out, closed_group_index + 1);
                state.pop();
                out(TokenEvent::GroupEnd, range);
                return;
            }
        }

        out(TokenEvent::Token(event), range);
    }

    fn next_pass(
        self,
        mut state: Self::State,
        end_marker: &Self::Marker,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        self.close_unmatched_groups(&mut state, end_marker, &mut out, 0);
        None
    }
}

impl<'a, Src: EventSource + 'a> ParenthesisMatcherPass<'a, Src> {
    fn close_unmatched_groups(
        &self,
        state: &mut ParenthesisMatcherState<Src::Marker>,
        end_marker: &Src::Marker,
        out: &mut impl FnMut(TokenEvent<'a>, Range<&Src::Marker>),
        target_len: usize,
    ) {
        while state.len() > target_len {
            let group = state.pop().unwrap();
            let expected = group.expected_closing_parenthesis;
            self.source.diagnostic(
                &group.group_start..end_marker,
                Severity::Error,
                format!("unmatched parenthesis: '{expected}' expected"),
            );
            out(TokenEvent::GroupEnd, end_marker..end_marker);
        }
    }
}

pub type ParenthesisMatcherState<Marker> = Vec<TokenGroupState<Marker>>;

#[derive(Clone, PartialEq)]
pub struct TokenGroupState<Marker: Clone + PartialEq> {
    group_start: Marker,
    expected_closing_parenthesis: char,
}

#[cfg(test)]
mod tests {
    use std::vec;

    use slate_kernel_notation_generic::{
        char_slice::{test_helpers::*, *},
        event::test_helpers::*,
    };

    use super::*;

    #[test]
    fn matched_parentheses() -> Result<(), Message> {
        test_parenthesis_matching("", Vec::new(), &[])?;
        test_parenthesis_matching(
            "abc",
            vec![ParenToken::Token(Token::Identifier("abc".into()))],
            &[],
        )?;
        test_parenthesis_matching("()", vec![ParenToken::Group('(', Vec::new())], &[])?;
        test_parenthesis_matching(
            "(abc)",
            vec![ParenToken::Group(
                '(',
                vec![ParenToken::Token(Token::Identifier("abc".into()))],
            )],
            &[],
        )?;
        test_parenthesis_matching(
            "a (b c [d|e]) f ⟦g⟧ h",
            vec![
                ParenToken::Token(Token::Identifier("a".into())),
                ParenToken::Group(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into())),
                        ParenToken::Token(Token::Identifier("c".into())),
                        ParenToken::Group(
                            '[',
                            vec![
                                ParenToken::Token(Token::Identifier("d".into())),
                                ParenToken::Token(Token::ReservedChar('|')),
                                ParenToken::Token(Token::Identifier("e".into())),
                            ],
                        ),
                    ],
                ),
                ParenToken::Token(Token::Identifier("f".into())),
                ParenToken::Group('⟦', vec![ParenToken::Token(Token::Identifier("g".into()))]),
                ParenToken::Token(Token::Identifier("h".into())),
            ],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn unmatched_parentheses() -> Result<(), Message> {
        test_parenthesis_matching(
            "(",
            vec![ParenToken::Group('(', Vec::new())],
            &[TestDiagnosticMessage {
                range_text: "(".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis: ')' expected".into(),
            }],
        )?;
        test_parenthesis_matching(
            "a (b c",
            vec![
                ParenToken::Token(Token::Identifier("a".into())),
                ParenToken::Group(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into())),
                        ParenToken::Token(Token::Identifier("c".into())),
                    ],
                ),
            ],
            &[TestDiagnosticMessage {
                range_text: "(b c".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis: ')' expected".into(),
            }],
        )?;
        test_parenthesis_matching(
            "a (b [c) d",
            vec![
                ParenToken::Token(Token::Identifier("a".into())),
                ParenToken::Group(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into())),
                        ParenToken::Group(
                            '[',
                            vec![ParenToken::Token(Token::Identifier("c".into()))],
                        ),
                    ],
                ),
                ParenToken::Token(Token::Identifier("d".into())),
            ],
            &[TestDiagnosticMessage {
                range_text: "[c".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis: ']' expected".into(),
            }],
        )?;
        test_parenthesis_matching(
            "a (b (c [d [e] f) g) h",
            vec![
                ParenToken::Token(Token::Identifier("a".into())),
                ParenToken::Group(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into())),
                        ParenToken::Group(
                            '(',
                            vec![
                                ParenToken::Token(Token::Identifier("c".into())),
                                ParenToken::Group(
                                    '[',
                                    vec![
                                        ParenToken::Token(Token::Identifier("d".into())),
                                        ParenToken::Group(
                                            '[',
                                            vec![ParenToken::Token(Token::Identifier("e".into()))],
                                        ),
                                        ParenToken::Token(Token::Identifier("f".into())),
                                    ],
                                ),
                            ],
                        ),
                        ParenToken::Token(Token::Identifier("g".into())),
                    ],
                ),
                ParenToken::Token(Token::Identifier("h".into())),
            ],
            &[TestDiagnosticMessage {
                range_text: "[d [e] f".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis: ']' expected".into(),
            }],
        )?;
        Ok(())
    }

    enum ParenToken<'a> {
        Token(Token<'a>),
        Group(char, Vec<ParenToken<'a>>),
    }

    impl<'a> IntoEvents<TokenEvent<'a>> for ParenToken<'a> {
        fn fill_events(self, result: &mut Vec<TokenEvent<'a>>) {
            match self {
                ParenToken::Token(token) => result.push(TokenEvent::Token(token)),
                ParenToken::Group(paren, contents) => {
                    result.push(TokenEvent::GroupStart(paren));
                    contents.fill_events(result);
                    result.push(TokenEvent::GroupEnd);
                }
            }
        }
    }

    fn test_parenthesis_matching(
        input: &str,
        expected_token_groups: Vec<ParenToken>,
        expected_diagnostics: &[TestDiagnosticMessage],
    ) -> Result<(), Message> {
        let mut token_events = Vec::new();
        let token_sink = TranslatorInst::new(ParenthesisMatcher, &mut token_events);
        let char_sink = TranslatorInst::new(Tokenizer, token_sink);
        let diag_sink = DiagnosticsRecorder::new(input);
        let source = CharSliceEventSource::new(input, &diag_sink)?;
        source.run(char_sink);
        assert_eq!(token_events, expected_token_groups.into_events());
        assert_eq!(diag_sink.diagnostics(), expected_diagnostics);
        Ok(())
    }
}
