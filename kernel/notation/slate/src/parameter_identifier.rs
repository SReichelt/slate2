use std::{borrow::Cow, marker::PhantomData, ops::Range, rc::Rc};

use slate_kernel_notation_generic::{event::*, event_translator::*};

use crate::{metamodel::*, parenthesis_matcher::*, tokenizer::*};

// `ParameterEvent` serializes `ParamToken` (defined in tests below) into events.
#[derive(Clone, PartialEq, Debug)]
pub enum ParameterEvent<'a> {
    MetaModel(MetaModelRef),
    ParamGroupStart,
    ParamGroupEnd,
    ParamNotationStart,
    ParamNotationEnd,
    ObjectStart,
    ObjectEnd,
    Token(TokenEvent<'a>),
}

impl Event for ParameterEvent<'_> {}

pub struct ParameterIdentifier {
    metamodel_getter: Rc<dyn MetaModelGetter>,
}

impl ParameterIdentifier {
    pub fn new(metamodel_getter: impl MetaModelGetter + 'static) -> Self {
        ParameterIdentifier {
            metamodel_getter: Rc::new(metamodel_getter),
        }
    }
}

impl<'a> EventTranslator<'a> for ParameterIdentifier {
    type In = TokenEvent<'a>;
    type Out = ParameterEvent<'a>;
    type Pass<Src: EventSource + 'a> = ParameterIdentifierPass<'a, Src>;

    fn start<Src: EventSource + 'a>(
        &self,
        source: Src,
        _special_ops: <Self::In as Event>::SpecialOps<'a, Src::Marker>,
    ) -> Self::Pass<Src> {
        ParameterIdentifierPass {
            metamodel_getter: self.metamodel_getter.clone(),
            source,
            _phantom_a: PhantomData,
        }
    }
}

pub struct ParameterIdentifierPass<'a, Src: EventSource + 'a> {
    metamodel_getter: Rc<dyn MetaModelGetter>,
    source: Src,
    _phantom_a: PhantomData<&'a ()>,
}

impl<'a, Src: EventSource + 'a> EventTranslatorPass for ParameterIdentifierPass<'a, Src> {
    type In = TokenEvent<'a>;
    type Out = ParameterEvent<'a>;
    type Marker = Src::Marker;
    type State = ParameterIdentifierState<'a, Src::Marker>;

    fn new_state(&self) -> Self::State {
        ParameterIdentifierState {
            metamodel_state: MetaModelState::Start,
            list_state: ParameterListState::new(None),
        }
    }

    fn event(
        &self,
        state: &mut Self::State,
        event: Self::In,
        range: Range<&Self::Marker>,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) {
        match &state.metamodel_state {
            MetaModelState::Start => {
                if let TokenEvent::Token(Token::Keyword(keyword)) = event {
                    if keyword == "slate" {
                        state.metamodel_state = MetaModelState::AfterKeyword;
                    } else {
                        self.source.diagnostic(
                            range,
                            Severity::Error,
                            format!("keyword 'slate' expected"),
                        );
                        state.metamodel_state = MetaModelState::Failed;
                    }
                } else {
                    self.source.diagnostic(
                        range,
                        Severity::Error,
                        format!("metamodel reference expected"),
                    );
                    state.metamodel_state = MetaModelState::Failed;
                }
            }

            MetaModelState::AfterKeyword => {
                if let TokenEvent::Token(Token::DoubleQuotedString(name)) = event {
                    state.metamodel_state = MetaModelState::AfterName {
                        name,
                        name_range: range.start.clone()..range.end.clone(),
                    };
                } else {
                    self.source.diagnostic(
                        range,
                        Severity::Error,
                        format!("metamodel name must be a string"),
                    );
                    state.metamodel_state = MetaModelState::Failed;
                }
            }

            MetaModelState::AfterName { name, name_range } => {
                if let TokenEvent::Token(Token::ReservedChar(';')) = event {
                    match self.metamodel_getter.metamodel(name) {
                        Ok(metamodel) => {
                            out(
                                ParameterEvent::MetaModel(metamodel.clone()),
                                &name_range.start..&name_range.end,
                            );
                            state.metamodel_state = MetaModelState::Succeeded(metamodel);
                        }
                        Err(err) => {
                            self.source.diagnostic(
                                &name_range.start..&name_range.end,
                                Severity::Error,
                                err.to_string(),
                            );
                            state.metamodel_state = MetaModelState::Failed;
                        }
                    }
                } else {
                    self.source
                        .diagnostic(range, Severity::Error, format!("';' expected"));
                    state.metamodel_state = MetaModelState::Failed;
                }
            }

            MetaModelState::Succeeded(metamodel) => {
                self.parameter_list_event(
                    &mut state.list_state,
                    event,
                    range,
                    &mut out,
                    metamodel.0.as_ref(),
                );
            }

            MetaModelState::Failed => {}
        }
    }

    fn next_pass(
        self,
        mut state: Self::State,
        end_marker: &Self::Marker,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        match &state.metamodel_state {
            MetaModelState::Start
            | MetaModelState::AfterKeyword
            | MetaModelState::AfterName {
                name: _,
                name_range: _,
            } => {
                self.source.diagnostic(
                    end_marker..end_marker,
                    Severity::Error,
                    format!("incomplete file header"),
                );
            }

            MetaModelState::Succeeded(metamodel) => {
                if let Some(group_state) = &mut state.list_state.current_group {
                    self.source.diagnostic(
                        end_marker..end_marker,
                        Severity::Error,
                        format!("';' expected"),
                    );
                    if !self.parameter_group_event(
                        group_state,
                        TokenEvent::GroupEnd,
                        end_marker..end_marker,
                        &mut out,
                        metamodel.0.as_ref(),
                    ) {
                        out(
                            ParameterEvent::ParamGroupEnd,
                            &group_state.current_end..&group_state.current_end,
                        );
                    }
                }
            }

            MetaModelState::Failed => {}
        }

        None
    }
}

// Consumes and outputs the event if it is part of an inner group or parameterization. Otherwise
// returns the event again, so that the client can decide to just output it, or to end the
// expression and then process it.
impl<'a, Src: EventSource + 'a> ParameterIdentifierPass<'a, Src> {
    fn expression_event<'b>(
        &self,
        state: &mut ExpressionState<Src::Marker>,
        event: TokenEvent<'a>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        metamodel: &dyn MetaModel,
        allow_parameterization: bool,
        allow_objects: bool,
    ) -> Option<(TokenEvent<'a>, Range<&'b Src::Marker>)> {
        match state {
            ExpressionState::Start => {
                if allow_parameterization {
                    if let TokenEvent::GroupStart(paren) = event {
                        if let Some(_) = metamodel.parameterization(paren) {
                            *state = ExpressionState::Parameterization(Box::new(
                                ParameterListState::new(None),
                            ));
                            return None;
                        }
                    }
                }
                *state = ExpressionState::TopLevel { after_dot: false };
                self.expression_event(
                    state,
                    event,
                    range,
                    out,
                    metamodel,
                    allow_parameterization,
                    allow_objects,
                )
            }

            ExpressionState::Parameterization(list_state) => {
                if !self.parameter_list_event(list_state.as_mut(), event, range, out, metamodel) {
                    *state = ExpressionState::Start;
                }
                None
            }

            ExpressionState::TopLevel { after_dot } => {
                if let TokenEvent::GroupStart(paren) = event {
                    if allow_objects && !*after_dot {
                        if let Some(object) = metamodel.object(paren) {
                            out(ParameterEvent::ObjectStart, range);
                            *state = ExpressionState::Object(Box::new(ParameterListState::new(
                                object.param_delimiter(),
                            )));
                            return None;
                        }
                    }
                    out(ParameterEvent::Token(event), range);
                    *state = ExpressionState::Group(Box::new(ExpressionState::Start));
                    None
                } else {
                    *after_dot = false;
                    if let TokenEvent::Token(Token::ReservedChar(c)) = event {
                        if c == ',' || c == ';' {
                            *state = ExpressionState::Start;
                        } else if c == '.' {
                            *after_dot = true;
                        }
                    }
                    Some((event, range))
                }
            }

            ExpressionState::Group(group) => {
                if let Some((event, range)) =
                    self.expression_event(group, event, range, out, metamodel, true, allow_objects)
                {
                    if let TokenEvent::GroupEnd = event {
                        *state = ExpressionState::TopLevel { after_dot: false };
                    }
                    out(ParameterEvent::Token(event), range);
                }
                None
            }

            ExpressionState::Object(list_state) => {
                if !self.parameter_list_event(
                    list_state.as_mut(),
                    event,
                    range.clone(),
                    out,
                    metamodel,
                ) {
                    *state = ExpressionState::TopLevel { after_dot: false };
                    out(ParameterEvent::ObjectEnd, range);
                }
                None
            }
        }
    }

    fn parameter_list_event(
        &self,
        state: &mut ParameterListState<Src::Marker>,
        event: TokenEvent<'a>,
        range: Range<&Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        metamodel: &dyn MetaModel,
    ) -> bool {
        let is_group_end = event == TokenEvent::GroupEnd;

        if let Some(expr_state) = &mut state.after_special_delimiter {
            if let Some((event, range)) = self.expression_event(
                expr_state,
                event,
                range.clone(),
                out,
                metamodel,
                false,
                true,
            ) {
                if is_group_end {
                    return false;
                }
                out(ParameterEvent::Token(event), range);
            }
        } else {
            let is_special_delimiter = matches!(event, TokenEvent::Token(Token::ReservedChar(c)) if Some(c) == state.special_delimiter);

            if let Some(group_state) = &mut state.current_group {
                if !self.parameter_group_event(group_state, event, range, out, metamodel) {
                    out(
                        ParameterEvent::ParamGroupEnd,
                        &group_state.current_end..&group_state.current_end,
                    );
                    state.current_group = None;
                    if is_group_end {
                        return false;
                    }
                    if is_special_delimiter {
                        state.after_special_delimiter = Some(ExpressionState::Start);
                    }
                }
            } else {
                if is_group_end {
                    return false;
                }
                if is_special_delimiter {
                    state.after_special_delimiter = Some(ExpressionState::Start);
                } else {
                    state.current_group = Some(ParameterGroupState {
                        special_delimiter: state.special_delimiter,
                        current_end: range.start.clone(),
                        content_state: ParameterGroupContentState::Start,
                    });
                    out(ParameterEvent::ParamGroupStart, range.start..range.start);
                    return self.parameter_list_event(state, event, range, out, metamodel);
                }
            }
        }

        true
    }

    fn parameter_group_event(
        &self,
        state: &mut ParameterGroupState<Src::Marker>,
        event: TokenEvent<'a>,
        range: Range<&Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        metamodel: &dyn MetaModel,
    ) -> bool {
        match &mut state.content_state {
            ParameterGroupContentState::Start => {
                if let TokenEvent::Token(Token::ReservedChar(c)) = event {
                    if c == ';' || Some(c) == state.special_delimiter {
                        return false;
                    }
                }
                if let TokenEvent::GroupStart(paren) = event {
                    if let Some(_) = metamodel.parameterization(paren) {
                        state.content_state = ParameterGroupContentState::Parameterization(
                            Box::new(ParameterListState::new(None)),
                        );
                        return true;
                    }
                }
                state.content_state = ParameterGroupContentState::Notation(ExpressionState::Start);
                return self.parameter_group_event(state, event, range, out, metamodel);
            }

            ParameterGroupContentState::Parameterization(list_state) => {
                if !self.parameter_list_event(
                    list_state.as_mut(),
                    event,
                    range.clone(),
                    out,
                    metamodel,
                ) {
                    state.content_state = ParameterGroupContentState::Start;
                }
                return true;
            }

            ParameterGroupContentState::Notation(expr_state) => {
                if *expr_state == ExpressionState::Start {
                    let notation_end = || {
                        self.source.diagnostic(
                            range.start..range.start,
                            Severity::Error,
                            format!("parameter expected"),
                        )
                    };

                    match event {
                        TokenEvent::Token(Token::ReservedChar(',')) => {
                            notation_end();
                            return true;
                        }
                        TokenEvent::Token(Token::DefinitionSymbol(_))
                        | TokenEvent::Token(Token::Keyword(_)) => {
                            notation_end();
                            state.content_state =
                                ParameterGroupContentState::Data(ExpressionState::Start);
                            return self.parameter_group_event(state, event, range, out, metamodel);
                        }
                        TokenEvent::GroupEnd => {
                            notation_end();
                            return false;
                        }
                        TokenEvent::Token(Token::ReservedChar(c))
                            if c == ';' || Some(c) == state.special_delimiter =>
                        {
                            notation_end();
                            return false;
                        }
                        _ => {
                            out(ParameterEvent::ParamNotationStart, range.start..range.start);
                            state.current_end = range.start.clone();
                        }
                    }
                }

                if let Some((event, range)) = self.expression_event(
                    expr_state,
                    event,
                    range.clone(),
                    out,
                    metamodel,
                    false,
                    false,
                ) {
                    let mut notation_end = || {
                        out(
                            ParameterEvent::ParamNotationEnd,
                            &state.current_end..&state.current_end,
                        );
                        *expr_state = ExpressionState::Start;
                    };

                    match event {
                        TokenEvent::Token(Token::ReservedChar(',')) => notation_end(),
                        TokenEvent::Token(Token::DefinitionSymbol(_))
                        | TokenEvent::Token(Token::Keyword(_)) => {
                            notation_end();
                            state.content_state =
                                ParameterGroupContentState::Data(ExpressionState::Start);
                            return self.parameter_group_event(state, event, range, out, metamodel);
                        }
                        TokenEvent::GroupEnd => {
                            notation_end();
                            return false;
                        }
                        TokenEvent::Token(Token::ReservedChar(c))
                            if c == ';' || Some(c) == state.special_delimiter =>
                        {
                            notation_end();
                            return false;
                        }
                        event => out(ParameterEvent::Token(event), range),
                    }
                }
            }

            ParameterGroupContentState::Data(expr_state) => {
                if let Some((event, range)) = self.expression_event(
                    expr_state,
                    event,
                    range.clone(),
                    out,
                    metamodel,
                    false,
                    true,
                ) {
                    match event {
                        TokenEvent::GroupEnd => {
                            return false;
                        }
                        TokenEvent::Token(Token::ReservedChar(c))
                            if c == ';' || Some(c) == state.special_delimiter =>
                        {
                            return false;
                        }
                        event => out(ParameterEvent::Token(event), range),
                    }
                }
            }
        }

        state.current_end = range.end.clone();
        true
    }
}

#[derive(Clone, PartialEq)]
pub struct ParameterIdentifierState<'a, Marker: Clone + PartialEq> {
    metamodel_state: MetaModelState<'a, Marker>,
    list_state: ParameterListState<Marker>,
}

#[derive(Clone, PartialEq)]
enum MetaModelState<'a, Marker: Clone + PartialEq> {
    Start,
    AfterKeyword,
    AfterName {
        name: Cow<'a, str>,
        name_range: Range<Marker>,
    },
    Succeeded(MetaModelRef),
    Failed,
}

#[derive(Clone, PartialEq)]
enum ExpressionState<Marker: Clone + PartialEq> {
    Start,
    Parameterization(Box<ParameterListState<Marker>>),
    TopLevel { after_dot: bool },
    Group(Box<ExpressionState<Marker>>),
    Object(Box<ParameterListState<Marker>>),
}

#[derive(Clone, PartialEq)]
struct ParameterListState<Marker: Clone + PartialEq> {
    special_delimiter: Option<char>,
    current_group: Option<ParameterGroupState<Marker>>,
    after_special_delimiter: Option<ExpressionState<Marker>>,
}

impl<Marker: Clone + PartialEq> ParameterListState<Marker> {
    fn new(special_delimiter: Option<char>) -> Self {
        ParameterListState {
            special_delimiter,
            current_group: None,
            after_special_delimiter: None,
        }
    }
}

#[derive(Clone, PartialEq)]
struct ParameterGroupState<Marker: Clone + PartialEq> {
    special_delimiter: Option<char>,
    current_end: Marker,
    content_state: ParameterGroupContentState<Marker>,
}

#[derive(Clone, PartialEq)]
enum ParameterGroupContentState<Marker: Clone + PartialEq> {
    Start,
    Parameterization(Box<ParameterListState<Marker>>),
    Notation(ExpressionState<Marker>),
    Data(ExpressionState<Marker>),
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use slate_kernel_notation_generic::{
        char_slice::{test_helpers::*, *},
        event::test_helpers::*,
    };

    use crate::{metamodel::test_helpers::*, tokenizer::*};

    use super::*;

    #[test]
    fn globals() -> Result<(), Message> {
        test_parameter_identification(
            "%slate \"test\";",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: Vec::new(),
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\";;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: Vec::new(),
                    data: Vec::new(),
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                    }],
                    data: Vec::new(),
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x;;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![
                    ParameterGroup {
                        parameterizations: Vec::new(),
                        params: vec![Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                        }],
                        data: Vec::new(),
                    },
                    ParameterGroup {
                        parameterizations: Vec::new(),
                        params: Vec::new(),
                        data: Vec::new(),
                    },
                ],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x : T;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                        ParamToken::Token(Token::Identifier("T".into())),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x : T := y;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                        ParamToken::Token(Token::Identifier("T".into())),
                        ParamToken::Token(Token::DefinitionSymbol(":=".into())),
                        ParamToken::Token(Token::Identifier("y".into())),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x : T; y : U;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![
                    ParameterGroup {
                        parameterizations: Vec::new(),
                        params: vec![Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                        }],
                        data: vec![
                            ParamToken::Token(Token::DefinitionSymbol(":".into())),
                            ParamToken::Token(Token::Identifier("T".into())),
                        ],
                    },
                    ParameterGroup {
                        parameterizations: Vec::new(),
                        params: vec![Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("y".into()))],
                        }],
                        data: vec![
                            ParamToken::Token(Token::DefinitionSymbol(":".into())),
                            ParamToken::Token(Token::Identifier("U".into())),
                        ],
                    },
                ],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x y;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![
                            ParamToken::Token(Token::Identifier("x".into())),
                            ParamToken::Token(Token::Identifier("y".into())),
                        ],
                    }],
                    data: Vec::new(),
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x y %z(a;b);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![
                            ParamToken::Token(Token::Identifier("x".into())),
                            ParamToken::Token(Token::Identifier("y".into())),
                        ],
                    }],
                    data: vec![
                        ParamToken::Token(Token::Keyword("z".into())),
                        ParamToken::Group(
                            '(',
                            vec![
                                ParamToken::Token(Token::Identifier("a".into())),
                                ParamToken::Token(Token::ReservedChar(';')),
                                ParamToken::Token(Token::Identifier("b".into())),
                            ],
                        ),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y,z);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![
                            ParamToken::Token(Token::Identifier("x".into())),
                            ParamToken::Group(
                                '(',
                                vec![
                                    ParamToken::Token(Token::Identifier("y".into())),
                                    ParamToken::Token(Token::ReservedChar(',')),
                                    ParamToken::Token(Token::Identifier("z".into())),
                                ],
                            ),
                        ],
                    }],
                    data: Vec::new(),
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x,y;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![
                        Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                        },
                        Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("y".into()))],
                        },
                    ],
                    data: Vec::new(),
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x,y : T;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![
                        Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                        },
                        Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("y".into()))],
                        },
                    ],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                        ParamToken::Token(Token::Identifier("T".into())),
                    ],
                }],
            },
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn parameterizations() -> Result<(), Message> {
        test_parameter_identification(
            "%slate \"test\"; [b : B] a : A;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: vec![ParameterGroup {
                        parameterizations: Vec::new(),
                        params: vec![Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("b".into()))],
                        }],
                        data: vec![
                            ParamToken::Token(Token::DefinitionSymbol(":".into())),
                            ParamToken::Token(Token::Identifier("B".into())),
                        ],
                    }],
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("a".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                        ParamToken::Token(Token::Identifier("A".into())),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[d : D] b,c : B] a : A;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: vec![ParameterGroup {
                        parameterizations: vec![ParameterGroup {
                            parameterizations: Vec::new(),
                            params: vec![Parameter {
                                notation: vec![ParamToken::Token(Token::Identifier("d".into()))],
                            }],
                            data: vec![
                                ParamToken::Token(Token::DefinitionSymbol(":".into())),
                                ParamToken::Token(Token::Identifier("D".into())),
                            ],
                        }],
                        params: vec![
                            Parameter {
                                notation: vec![ParamToken::Token(Token::Identifier("b".into()))],
                            },
                            Parameter {
                                notation: vec![ParamToken::Token(Token::Identifier("c".into()))],
                            },
                        ],
                        data: vec![
                            ParamToken::Token(Token::DefinitionSymbol(":".into())),
                            ParamToken::Token(Token::Identifier("B".into())),
                        ],
                    }],
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("a".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                        ParamToken::Token(Token::Identifier("A".into())),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; a := f([b : B] b);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("a".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":=".into())),
                        ParamToken::Token(Token::Identifier("f".into())),
                        ParamToken::Group(
                            '(',
                            vec![
                                ParamToken::ParamGroup(ParameterGroup {
                                    parameterizations: Vec::new(),
                                    params: vec![Parameter {
                                        notation: vec![ParamToken::Token(Token::Identifier(
                                            "b".into(),
                                        ))],
                                    }],
                                    data: vec![
                                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                                        ParamToken::Token(Token::Identifier("B".into())),
                                    ],
                                }),
                                ParamToken::Token(Token::Identifier("b".into())),
                            ],
                        ),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; a := f[[b : B] b, [[d : D] ⟦e : E⟧ c[d,e] : C] c[0,1]];",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("a".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":=".into())),
                        ParamToken::Token(Token::Identifier("f".into())),
                        ParamToken::Group(
                            '[',
                            vec![
                                ParamToken::ParamGroup(ParameterGroup {
                                    parameterizations: Vec::new(),
                                    params: vec![Parameter {
                                        notation: vec![ParamToken::Token(Token::Identifier(
                                            "b".into(),
                                        ))],
                                    }],
                                    data: vec![
                                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                                        ParamToken::Token(Token::Identifier("B".into())),
                                    ],
                                }),
                                ParamToken::Token(Token::Identifier("b".into())),
                                ParamToken::Token(Token::ReservedChar(',')),
                                ParamToken::ParamGroup(ParameterGroup {
                                    parameterizations: vec![
                                        ParameterGroup {
                                            parameterizations: Vec::new(),
                                            params: vec![Parameter {
                                                notation: vec![ParamToken::Token(
                                                    Token::Identifier("d".into()),
                                                )],
                                            }],
                                            data: vec![
                                                ParamToken::Token(Token::DefinitionSymbol(
                                                    ":".into(),
                                                )),
                                                ParamToken::Token(Token::Identifier("D".into())),
                                            ],
                                        },
                                        ParameterGroup {
                                            parameterizations: Vec::new(),
                                            params: vec![Parameter {
                                                notation: vec![ParamToken::Token(
                                                    Token::Identifier("e".into()),
                                                )],
                                            }],
                                            data: vec![
                                                ParamToken::Token(Token::DefinitionSymbol(
                                                    ":".into(),
                                                )),
                                                ParamToken::Token(Token::Identifier("E".into())),
                                            ],
                                        },
                                    ],
                                    params: vec![Parameter {
                                        notation: vec![
                                            ParamToken::Token(Token::Identifier("c".into())),
                                            ParamToken::Group(
                                                '[',
                                                vec![
                                                    ParamToken::Token(Token::Identifier(
                                                        "d".into(),
                                                    )),
                                                    ParamToken::Token(Token::ReservedChar(',')),
                                                    ParamToken::Token(Token::Identifier(
                                                        "e".into(),
                                                    )),
                                                ],
                                            ),
                                        ],
                                    }],
                                    data: vec![
                                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                                        ParamToken::Token(Token::Identifier("C".into())),
                                    ],
                                }),
                                ParamToken::Token(Token::Identifier("c".into())),
                                ParamToken::Group(
                                    '[',
                                    vec![
                                        ParamToken::Token(Token::Number("0".into())),
                                        ParamToken::Token(Token::ReservedChar(',')),
                                        ParamToken::Token(Token::Number("1".into())),
                                    ],
                                ),
                            ],
                        ),
                    ],
                }],
            },
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn objects() -> Result<(), Message> {
        test_parameter_identification(
            "%slate \"test\"; T := {};",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("T".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":=".into())),
                        ParamToken::Object(Vec::new(), Vec::new()),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {x};",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("T".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":=".into())),
                        ParamToken::Object(
                            vec![ParameterGroup {
                                parameterizations: Vec::new(),
                                params: vec![Parameter {
                                    notation: vec![ParamToken::Token(Token::Identifier(
                                        "x".into(),
                                    ))],
                                }],
                                data: Vec::new(),
                            }],
                            Vec::new(),
                        ),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {|x};",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("T".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":=".into())),
                        ParamToken::Object(
                            Vec::new(),
                            vec![ParamToken::Token(Token::Identifier("x".into()))],
                        ),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {[i : I] x,x' : X; [j : J] y,y' : Y | a | b} | {z};",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("T".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":=".into())),
                        ParamToken::Object(
                            vec![
                                ParameterGroup {
                                    parameterizations: vec![ParameterGroup {
                                        parameterizations: Vec::new(),
                                        params: vec![Parameter {
                                            notation: vec![ParamToken::Token(Token::Identifier(
                                                "i".into(),
                                            ))],
                                        }],
                                        data: vec![
                                            ParamToken::Token(Token::DefinitionSymbol(":".into())),
                                            ParamToken::Token(Token::Identifier("I".into())),
                                        ],
                                    }],
                                    params: vec![
                                        Parameter {
                                            notation: vec![ParamToken::Token(Token::Identifier(
                                                "x".into(),
                                            ))],
                                        },
                                        Parameter {
                                            notation: vec![ParamToken::Token(Token::Identifier(
                                                "x'".into(),
                                            ))],
                                        },
                                    ],
                                    data: vec![
                                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                                        ParamToken::Token(Token::Identifier("X".into())),
                                    ],
                                },
                                ParameterGroup {
                                    parameterizations: vec![ParameterGroup {
                                        parameterizations: Vec::new(),
                                        params: vec![Parameter {
                                            notation: vec![ParamToken::Token(Token::Identifier(
                                                "j".into(),
                                            ))],
                                        }],
                                        data: vec![
                                            ParamToken::Token(Token::DefinitionSymbol(":".into())),
                                            ParamToken::Token(Token::Identifier("J".into())),
                                        ],
                                    }],
                                    params: vec![
                                        Parameter {
                                            notation: vec![ParamToken::Token(Token::Identifier(
                                                "y".into(),
                                            ))],
                                        },
                                        Parameter {
                                            notation: vec![ParamToken::Token(Token::Identifier(
                                                "y'".into(),
                                            ))],
                                        },
                                    ],
                                    data: vec![
                                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                                        ParamToken::Token(Token::Identifier("Y".into())),
                                    ],
                                },
                            ],
                            vec![
                                ParamToken::Token(Token::Identifier("a".into())),
                                ParamToken::Token(Token::ReservedChar('|')),
                                ParamToken::Token(Token::Identifier("b".into())),
                            ],
                        ),
                        ParamToken::Token(Token::ReservedChar('|')),
                        ParamToken::Object(
                            vec![ParameterGroup {
                                parameterizations: Vec::new(),
                                params: vec![Parameter {
                                    notation: vec![ParamToken::Token(Token::Identifier(
                                        "z".into(),
                                    ))],
                                }],
                                data: Vec::new(),
                            }],
                            Vec::new(),
                        ),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; ℕ := {0; [n : ℕ] S(n)};",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("ℕ".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":=".into())),
                        ParamToken::Object(
                            vec![
                                ParameterGroup {
                                    parameterizations: Vec::new(),
                                    params: vec![Parameter {
                                        notation: vec![ParamToken::Token(Token::Number(
                                            "0".into(),
                                        ))],
                                    }],
                                    data: Vec::new(),
                                },
                                ParameterGroup {
                                    parameterizations: vec![ParameterGroup {
                                        parameterizations: Vec::new(),
                                        params: vec![Parameter {
                                            notation: vec![ParamToken::Token(Token::Identifier(
                                                "n".into(),
                                            ))],
                                        }],
                                        data: vec![
                                            ParamToken::Token(Token::DefinitionSymbol(":".into())),
                                            ParamToken::Token(Token::Identifier("ℕ".into())),
                                        ],
                                    }],
                                    params: vec![Parameter {
                                        notation: vec![
                                            ParamToken::Token(Token::Identifier("S".into())),
                                            ParamToken::Group(
                                                '(',
                                                vec![ParamToken::Token(Token::Identifier(
                                                    "n".into(),
                                                ))],
                                            ),
                                        ],
                                    }],
                                    data: Vec::new(),
                                },
                            ],
                            Vec::new(),
                        ),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x := T.{t};",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":=".into())),
                        ParamToken::Token(Token::Identifier("T".into())),
                        ParamToken::Token(Token::ReservedChar('.')),
                        ParamToken::Group(
                            '{',
                            vec![ParamToken::Token(Token::Identifier("t".into()))],
                        ),
                    ],
                }],
            },
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn top_level_errors() -> Result<(), Message> {
        test_parameter_identification(
            "",
            Document {
                metamodel: None,
                definitions: Vec::new(),
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "incomplete file header".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"",
            Document {
                metamodel: None,
                definitions: Vec::new(),
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "incomplete file header".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"unknown\";",
            Document {
                metamodel: None,
                definitions: Vec::new(),
            },
            &[TestDiagnosticMessage {
                range_text: "\"unknown\"".into(),
                severity: Severity::Error,
                msg: "unknown metamodel 'unknown'".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                    }],
                    data: Vec::new(),
                }],
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "';' expected".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x : T",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                    }],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                        ParamToken::Token(Token::Identifier("T".into())),
                    ],
                }],
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "';' expected".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x,,y : T;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![
                        Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("x".into()))],
                        },
                        Parameter {
                            notation: vec![ParamToken::Token(Token::Identifier("y".into()))],
                        },
                    ],
                    data: vec![
                        ParamToken::Token(Token::DefinitionSymbol(":".into())),
                        ParamToken::Token(Token::Identifier("T".into())),
                    ],
                }],
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "parameter expected".into(),
            }],
        )?;
        Ok(())
    }

    struct Document<'a> {
        metamodel: Option<MetaModelRef>,
        definitions: Vec<ParameterGroup<'a>>,
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for Document<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            if let Some(metamodel) = self.metamodel {
                result.push(ParameterEvent::MetaModel(metamodel));
            }
            self.definitions.fill_events(result);
        }
    }

    struct ParameterGroup<'a> {
        parameterizations: Vec<ParameterGroup<'a>>,
        params: Vec<Parameter<'a>>,
        data: Vec<ParamToken<'a>>,
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for ParameterGroup<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            result.push(ParameterEvent::ParamGroupStart);
            self.parameterizations.fill_events(result);
            self.params.fill_events(result);
            self.data.fill_events(result);
            result.push(ParameterEvent::ParamGroupEnd);
        }
    }

    struct Parameter<'a> {
        notation: Vec<ParamToken<'a>>,
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for Parameter<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            result.push(ParameterEvent::ParamNotationStart);
            self.notation.fill_events(result);
            result.push(ParameterEvent::ParamNotationEnd);
        }
    }

    enum ParamToken<'a> {
        Token(Token<'a>),
        Group(char, Vec<ParamToken<'a>>),
        ParamGroup(ParameterGroup<'a>),
        Object(Vec<ParameterGroup<'a>>, Vec<ParamToken<'a>>),
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for ParamToken<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            match self {
                ParamToken::Token(token) => {
                    result.push(ParameterEvent::Token(TokenEvent::Token(token)))
                }
                ParamToken::Group(paren, contents) => {
                    result.push(ParameterEvent::Token(TokenEvent::GroupStart(paren)));
                    contents.fill_events(result);
                    result.push(ParameterEvent::Token(TokenEvent::GroupEnd));
                }
                ParamToken::ParamGroup(param_group) => {
                    param_group.fill_events(result);
                }
                ParamToken::Object(params, data) => {
                    result.push(ParameterEvent::ObjectStart);
                    params.fill_events(result);
                    data.fill_events(result);
                    result.push(ParameterEvent::ObjectEnd);
                }
            }
        }
    }

    fn test_parameter_identification(
        input: &str,
        expected_document: Document,
        expected_diagnostics: &[TestDiagnosticMessage],
    ) -> Result<(), Message> {
        let mut param_events = Vec::new();
        let param_sink = TranslatorInst::new(
            ParameterIdentifier::new(TestMetaModelGetter),
            &mut param_events,
        );
        let token_sink = TranslatorInst::new(ParenthesisMatcher, param_sink);
        let char_sink = TranslatorInst::new(Tokenizer, token_sink);
        let diag_sink = DiagnosticsRecorder::new(input);
        let source = CharSliceEventSource::new(input, &diag_sink)?;
        source.run(char_sink);
        assert_eq!(param_events, expected_document.into_events());
        assert_eq!(diag_sink.diagnostics(), expected_diagnostics);
        Ok(())
    }
}
