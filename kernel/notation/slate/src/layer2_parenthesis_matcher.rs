use std::ops::Range;

use slate_kernel_notation_generic::{event::*, event_source::*, event_translator::*};

use crate::{chars::*, layer1_tokenizer::*};

// `TokenEvent` serializes `ParenToken` (defined in tests below) into events.
#[derive(Clone, PartialEq, Debug)]
pub enum TokenEvent<'a> {
    Token(Token<'a>),
    Paren(GroupEvent<char>),
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
        if let Token::ReservedChar(c, pre_isolation, post_isolation) = event {
            let mut is_symmetric_paren = false;

            if let Some(expected_closing_parenthesis) = matching_closing_parenthesis(c) {
                is_symmetric_paren = expected_closing_parenthesis == c;
                if !is_symmetric_paren
                    || (pre_isolation != TokenIsolation::StronglyConnected
                        && post_isolation == TokenIsolation::StronglyConnected)
                {
                    state.push(TokenGroupState {
                        group_start: range.start.clone(),
                        expected_closing_parenthesis,
                    });
                    self.output_paren_start(c, range, &mut out);
                    return;
                }
            }

            if is_closing_parenthesis(c)
                || (is_symmetric_paren
                    && pre_isolation == TokenIsolation::StronglyConnected
                    && post_isolation != TokenIsolation::StronglyConnected)
            {
                if let Some(closed_group_index) = state
                    .iter()
                    .rposition(|group| group.expected_closing_parenthesis == c)
                {
                    self.close_unmatched_groups(
                        state,
                        range.start,
                        &mut out,
                        closed_group_index + 1,
                    );
                    state.pop();
                    self.output_paren_end(range, &mut out);
                } else {
                    self.source.diagnostic(
                        range,
                        Severity::Error,
                        format!("unmatched parenthesis"),
                    );
                }
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
    fn output_paren_start(
        &self,
        c: char,
        range: Range<&Src::Marker>,
        out: &mut impl FnMut(TokenEvent<'a>, Range<&Src::Marker>),
    ) {
        self.source
            .range_event(RangeClassEvent::Start(RangeClass::Paren), range.start);
        out(TokenEvent::Paren(GroupEvent::Start(c)), range);
    }

    fn output_paren_end(
        &self,
        range: Range<&Src::Marker>,
        out: &mut impl FnMut(TokenEvent<'a>, Range<&Src::Marker>),
    ) {
        let end = range.end;
        out(TokenEvent::Paren(GroupEvent::End), range);
        self.source
            .range_event(RangeClassEvent::End(RangeClass::Paren), end);
    }

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
            self.output_paren_end(end_marker..end_marker, out);
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
        event_source::test_helpers::*,
    };

    use super::*;

    #[test]
    fn matched_parentheses() -> Result<(), Message> {
        test_parenthesis_matching("", Vec::new(), &[], Vec::new())?;
        test_parenthesis_matching(
            "abc",
            vec![ParenToken::Token(Token::Identifier(
                "abc".into(),
                IdentifierType::Unquoted,
            ))],
            &[],
            vec![RangeClassTreeNode::Text("abc")],
        )?;
        test_parenthesis_matching(
            "()",
            vec![ParenToken::Paren('(', Vec::new())],
            &[],
            vec![RangeClassTreeNode::Range(
                RangeClass::Paren,
                vec![RangeClassTreeNode::Text("()")],
            )],
        )?;
        test_parenthesis_matching(
            "(abc)",
            vec![ParenToken::Paren(
                '(',
                vec![ParenToken::Token(Token::Identifier(
                    "abc".into(),
                    IdentifierType::Unquoted,
                ))],
            )],
            &[],
            vec![RangeClassTreeNode::Range(
                RangeClass::Paren,
                vec![RangeClassTreeNode::Text("(abc)")],
            )],
        )?;
        test_parenthesis_matching(
            "|abc|",
            vec![ParenToken::Paren(
                '|',
                vec![ParenToken::Token(Token::Identifier(
                    "abc".into(),
                    IdentifierType::Unquoted,
                ))],
            )],
            &[],
            vec![RangeClassTreeNode::Range(
                RangeClass::Paren,
                vec![RangeClassTreeNode::Text("|abc|")],
            )],
        )?;
        test_parenthesis_matching(
            "(|abc|)",
            vec![ParenToken::Paren(
                '(',
                vec![ParenToken::Paren(
                    '|',
                    vec![ParenToken::Token(Token::Identifier(
                        "abc".into(),
                        IdentifierType::Unquoted,
                    ))],
                )],
            )],
            &[],
            vec![RangeClassTreeNode::Range(
                RangeClass::Paren,
                vec![
                    RangeClassTreeNode::Text("("),
                    RangeClassTreeNode::Range(
                        RangeClass::Paren,
                        vec![RangeClassTreeNode::Text("|abc|")],
                    ),
                    RangeClassTreeNode::Text(")"),
                ],
            )],
        )?;
        test_parenthesis_matching(
            "|(abc)|",
            vec![ParenToken::Paren(
                '|',
                vec![ParenToken::Paren(
                    '(',
                    vec![ParenToken::Token(Token::Identifier(
                        "abc".into(),
                        IdentifierType::Unquoted,
                    ))],
                )],
            )],
            &[],
            vec![RangeClassTreeNode::Range(
                RangeClass::Paren,
                vec![
                    RangeClassTreeNode::Text("|"),
                    RangeClassTreeNode::Range(
                        RangeClass::Paren,
                        vec![RangeClassTreeNode::Text("(abc)")],
                    ),
                    RangeClassTreeNode::Text("|"),
                ],
            )],
        )?;
        test_parenthesis_matching(
            "(|(abc)|)",
            vec![ParenToken::Paren(
                '(',
                vec![ParenToken::Paren(
                    '|',
                    vec![ParenToken::Paren(
                        '(',
                        vec![ParenToken::Token(Token::Identifier(
                            "abc".into(),
                            IdentifierType::Unquoted,
                        ))],
                    )],
                )],
            )],
            &[],
            vec![RangeClassTreeNode::Range(
                RangeClass::Paren,
                vec![
                    RangeClassTreeNode::Text("("),
                    RangeClassTreeNode::Range(
                        RangeClass::Paren,
                        vec![
                            RangeClassTreeNode::Text("|"),
                            RangeClassTreeNode::Range(
                                RangeClass::Paren,
                                vec![RangeClassTreeNode::Text("(abc)")],
                            ),
                            RangeClassTreeNode::Text("|"),
                        ],
                    ),
                    RangeClassTreeNode::Text(")"),
                ],
            )],
        )?;
        test_parenthesis_matching(
            "(%abc)",
            vec![ParenToken::Paren(
                '(',
                vec![ParenToken::Token(Token::Keyword("%abc".into()))],
            )],
            &[],
            vec![RangeClassTreeNode::Range(
                RangeClass::Paren,
                vec![
                    RangeClassTreeNode::Text("("),
                    RangeClassTreeNode::Range(
                        RangeClass::Keyword,
                        vec![RangeClassTreeNode::Text("%abc")],
                    ),
                    RangeClassTreeNode::Text(")"),
                ],
            )],
        )?;
        test_parenthesis_matching(
            "|a|^b",
            vec![
                ParenToken::Paren(
                    '|',
                    vec![ParenToken::Token(Token::Identifier(
                        "a".into(),
                        IdentifierType::Unquoted,
                    ))],
                ),
                ParenToken::Token(Token::ReservedChar(
                    '^',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                )),
                ParenToken::Token(Token::Identifier("b".into(), IdentifierType::Unquoted)),
            ],
            &[],
            vec![
                RangeClassTreeNode::Range(RangeClass::Paren, vec![RangeClassTreeNode::Text("|a|")]),
                RangeClassTreeNode::Text("^b"),
            ],
        )?;
        test_parenthesis_matching(
            "|a|⁻¹",
            vec![
                ParenToken::Paren(
                    '|',
                    vec![ParenToken::Token(Token::Identifier(
                        "a".into(),
                        IdentifierType::Unquoted,
                    ))],
                ),
                ParenToken::Token(Token::Identifier("⁻¹".into(), IdentifierType::Unquoted)),
            ],
            &[],
            vec![
                RangeClassTreeNode::Range(RangeClass::Paren, vec![RangeClassTreeNode::Text("|a|")]),
                RangeClassTreeNode::Text("⁻¹"),
            ],
        )?;
        test_parenthesis_matching(
            "|a²|⁻¹",
            vec![
                ParenToken::Paren(
                    '|',
                    vec![
                        ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                        ParenToken::Token(Token::Identifier("²".into(), IdentifierType::Unquoted)),
                    ],
                ),
                ParenToken::Token(Token::Identifier("⁻¹".into(), IdentifierType::Unquoted)),
            ],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![RangeClassTreeNode::Text("|a²|")],
                ),
                RangeClassTreeNode::Text("⁻¹"),
            ],
        )?;
        test_parenthesis_matching(
            "|a+(b-c)|⁻¹",
            vec![
                ParenToken::Paren(
                    '|',
                    vec![
                        ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                        ParenToken::Token(Token::Identifier("+".into(), IdentifierType::Unquoted)),
                        ParenToken::Paren(
                            '(',
                            vec![
                                ParenToken::Token(Token::Identifier(
                                    "b".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParenToken::Token(Token::Identifier(
                                    "-".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParenToken::Token(Token::Identifier(
                                    "c".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    ],
                ),
                ParenToken::Token(Token::Identifier("⁻¹".into(), IdentifierType::Unquoted)),
            ],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("|a+"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("(b-c)")],
                        ),
                        RangeClassTreeNode::Text("|"),
                    ],
                ),
                RangeClassTreeNode::Text("⁻¹"),
            ],
        )?;
        test_parenthesis_matching(
            "||",
            vec![
                ParenToken::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                )),
                ParenToken::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                )),
            ],
            &[],
            vec![RangeClassTreeNode::Text("||")],
        )?;
        test_parenthesis_matching(
            "|||",
            vec![
                ParenToken::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::Isolated,
                    TokenIsolation::WeaklyConnected,
                )),
                ParenToken::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::WeaklyConnected,
                )),
                ParenToken::Token(Token::ReservedChar(
                    '|',
                    TokenIsolation::WeaklyConnected,
                    TokenIsolation::Isolated,
                )),
            ],
            &[],
            vec![RangeClassTreeNode::Text("|||")],
        )?;
        test_parenthesis_matching(
            "a (b c [d|e]) f ⟦g ‖ h⟧ ‖i‖.|j|",
            vec![
                ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                ParenToken::Paren(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into(), IdentifierType::Unquoted)),
                        ParenToken::Token(Token::Identifier("c".into(), IdentifierType::Unquoted)),
                        ParenToken::Paren(
                            '[',
                            vec![
                                ParenToken::Token(Token::Identifier(
                                    "d".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParenToken::Token(Token::ReservedChar(
                                    '|',
                                    TokenIsolation::StronglyConnected,
                                    TokenIsolation::StronglyConnected,
                                )),
                                ParenToken::Token(Token::Identifier(
                                    "e".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    ],
                ),
                ParenToken::Token(Token::Identifier("f".into(), IdentifierType::Unquoted)),
                ParenToken::Paren(
                    '⟦',
                    vec![
                        ParenToken::Token(Token::Identifier("g".into(), IdentifierType::Unquoted)),
                        ParenToken::Token(Token::ReservedChar(
                            '‖',
                            TokenIsolation::Isolated,
                            TokenIsolation::Isolated,
                        )),
                        ParenToken::Token(Token::Identifier("h".into(), IdentifierType::Unquoted)),
                    ],
                ),
                ParenToken::Paren(
                    '‖',
                    vec![ParenToken::Token(Token::Identifier(
                        "i".into(),
                        IdentifierType::Unquoted,
                    ))],
                ),
                ParenToken::Token(Token::ReservedChar(
                    '.',
                    TokenIsolation::StronglyConnected,
                    TokenIsolation::StronglyConnected,
                )),
                ParenToken::Paren(
                    '|',
                    vec![ParenToken::Token(Token::Identifier(
                        "j".into(),
                        IdentifierType::Unquoted,
                    ))],
                ),
            ],
            &[],
            vec![
                RangeClassTreeNode::Text("a "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("(b c "),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("[d|e]")],
                        ),
                        RangeClassTreeNode::Text(")"),
                    ],
                ),
                RangeClassTreeNode::Text(" f "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![RangeClassTreeNode::Text("⟦g ‖ h⟧")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(RangeClass::Paren, vec![RangeClassTreeNode::Text("‖i‖")]),
                RangeClassTreeNode::Text("."),
                RangeClassTreeNode::Range(RangeClass::Paren, vec![RangeClassTreeNode::Text("|j|")]),
            ],
        )?;
        Ok(())
    }

    #[test]
    fn unmatched_parentheses() -> Result<(), Message> {
        test_parenthesis_matching(
            "(",
            vec![ParenToken::Paren('(', Vec::new())],
            &[TestDiagnosticMessage {
                range_text: "(".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis: ')' expected".into(),
            }],
            vec![RangeClassTreeNode::Range(
                RangeClass::Paren,
                vec![RangeClassTreeNode::Text("(")],
            )],
        )?;
        test_parenthesis_matching(
            ")",
            Vec::new(),
            &[TestDiagnosticMessage {
                range_text: ")".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis".into(),
            }],
            vec![RangeClassTreeNode::Text(")")],
        )?;
        test_parenthesis_matching(
            "a (b c",
            vec![
                ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                ParenToken::Paren(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into(), IdentifierType::Unquoted)),
                        ParenToken::Token(Token::Identifier("c".into(), IdentifierType::Unquoted)),
                    ],
                ),
            ],
            &[TestDiagnosticMessage {
                range_text: "(b c".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis: ')' expected".into(),
            }],
            vec![
                RangeClassTreeNode::Text("a "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![RangeClassTreeNode::Text("(b c")],
                ),
            ],
        )?;
        test_parenthesis_matching(
            "a b) c",
            vec![
                ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                ParenToken::Token(Token::Identifier("b".into(), IdentifierType::Unquoted)),
                ParenToken::Token(Token::Identifier("c".into(), IdentifierType::Unquoted)),
            ],
            &[TestDiagnosticMessage {
                range_text: ")".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis".into(),
            }],
            vec![RangeClassTreeNode::Text("a b) c")],
        )?;
        test_parenthesis_matching(
            "a (b [c) d",
            vec![
                ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                ParenToken::Paren(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into(), IdentifierType::Unquoted)),
                        ParenToken::Paren(
                            '[',
                            vec![ParenToken::Token(Token::Identifier(
                                "c".into(),
                                IdentifierType::Unquoted,
                            ))],
                        ),
                    ],
                ),
                ParenToken::Token(Token::Identifier("d".into(), IdentifierType::Unquoted)),
            ],
            &[TestDiagnosticMessage {
                range_text: "[c".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis: ']' expected".into(),
            }],
            vec![
                RangeClassTreeNode::Text("a "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("(b "),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("[c")],
                        ),
                        RangeClassTreeNode::Text(")"),
                    ],
                ),
                RangeClassTreeNode::Text(" d"),
            ],
        )?;
        test_parenthesis_matching(
            "a (b |c) d",
            vec![
                ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                ParenToken::Paren(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into(), IdentifierType::Unquoted)),
                        ParenToken::Paren(
                            '|',
                            vec![ParenToken::Token(Token::Identifier(
                                "c".into(),
                                IdentifierType::Unquoted,
                            ))],
                        ),
                    ],
                ),
                ParenToken::Token(Token::Identifier("d".into(), IdentifierType::Unquoted)),
            ],
            &[TestDiagnosticMessage {
                range_text: "|c".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis: '|' expected".into(),
            }],
            vec![
                RangeClassTreeNode::Text("a "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("(b "),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("|c")],
                        ),
                        RangeClassTreeNode::Text(")"),
                    ],
                ),
                RangeClassTreeNode::Text(" d"),
            ],
        )?;
        test_parenthesis_matching(
            "a (b] c) d",
            vec![
                ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                ParenToken::Paren(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into(), IdentifierType::Unquoted)),
                        ParenToken::Token(Token::Identifier("c".into(), IdentifierType::Unquoted)),
                    ],
                ),
                ParenToken::Token(Token::Identifier("d".into(), IdentifierType::Unquoted)),
            ],
            &[TestDiagnosticMessage {
                range_text: "]".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis".into(),
            }],
            vec![
                RangeClassTreeNode::Text("a "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![RangeClassTreeNode::Text("(b] c)")],
                ),
                RangeClassTreeNode::Text(" d"),
            ],
        )?;
        test_parenthesis_matching(
            "a (b| c) d",
            vec![
                ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                ParenToken::Paren(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into(), IdentifierType::Unquoted)),
                        ParenToken::Token(Token::Identifier("c".into(), IdentifierType::Unquoted)),
                    ],
                ),
                ParenToken::Token(Token::Identifier("d".into(), IdentifierType::Unquoted)),
            ],
            &[TestDiagnosticMessage {
                range_text: "|".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis".into(),
            }],
            vec![
                RangeClassTreeNode::Text("a "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![RangeClassTreeNode::Text("(b| c)")],
                ),
                RangeClassTreeNode::Text(" d"),
            ],
        )?;
        test_parenthesis_matching(
            "a (b (c [d [e] f) g) h",
            vec![
                ParenToken::Token(Token::Identifier("a".into(), IdentifierType::Unquoted)),
                ParenToken::Paren(
                    '(',
                    vec![
                        ParenToken::Token(Token::Identifier("b".into(), IdentifierType::Unquoted)),
                        ParenToken::Paren(
                            '(',
                            vec![
                                ParenToken::Token(Token::Identifier(
                                    "c".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParenToken::Paren(
                                    '[',
                                    vec![
                                        ParenToken::Token(Token::Identifier(
                                            "d".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        ParenToken::Paren(
                                            '[',
                                            vec![ParenToken::Token(Token::Identifier(
                                                "e".into(),
                                                IdentifierType::Unquoted,
                                            ))],
                                        ),
                                        ParenToken::Token(Token::Identifier(
                                            "f".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                ),
                            ],
                        ),
                        ParenToken::Token(Token::Identifier("g".into(), IdentifierType::Unquoted)),
                    ],
                ),
                ParenToken::Token(Token::Identifier("h".into(), IdentifierType::Unquoted)),
            ],
            &[TestDiagnosticMessage {
                range_text: "[d [e] f".into(),
                severity: Severity::Error,
                msg: "unmatched parenthesis: ']' expected".into(),
            }],
            vec![
                RangeClassTreeNode::Text("a "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("(b "),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("(c "),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("[d "),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![RangeClassTreeNode::Text("[e]")],
                                        ),
                                        RangeClassTreeNode::Text(" f"),
                                    ],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" g)"),
                    ],
                ),
                RangeClassTreeNode::Text(" h"),
            ],
        )?;
        Ok(())
    }

    enum ParenToken<'a> {
        Token(Token<'a>),
        Paren(char, Vec<ParenToken<'a>>),
    }

    impl<'a> IntoEvents<TokenEvent<'a>> for ParenToken<'a> {
        fn fill_events(self, result: &mut Vec<TokenEvent<'a>>) {
            match self {
                ParenToken::Token(token) => result.push(TokenEvent::Token(token)),
                ParenToken::Paren(paren, contents) => {
                    Self::group(
                        paren,
                        result,
                        |event| TokenEvent::Paren(event),
                        |result| contents.fill_events(result),
                    );
                }
            }
        }
    }

    fn test_parenthesis_matching(
        input: &str,
        expected_token_groups: Vec<ParenToken>,
        expected_diagnostics: &[TestDiagnosticMessage],
        expected_ranges: RangeClassTree,
    ) -> Result<(), Message> {
        let mut token_events = Vec::new();
        let token_sink = TranslatorInst::new(ParenthesisMatcher, &mut token_events);
        let char_sink = TranslatorInst::new(Tokenizer, token_sink);
        let diag_sink = DiagnosticsRecorder::new(input);
        let source = CharSliceEventSource::new(input, &diag_sink)?;
        source.run(char_sink);
        assert_eq!(token_events, expected_token_groups.into_events());
        let (diagnostics, range_events) = diag_sink.results();
        assert_eq!(diagnostics, expected_diagnostics);
        assert_eq!((range_events, input.len()), expected_ranges.into_events());
        Ok(())
    }
}
