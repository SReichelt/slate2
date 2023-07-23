use std::{borrow::Cow, mem::take, ops::Range, rc::Rc};

use slate_kernel_notation_generic::{event::*, event_translator::*};

use crate::{
    chars::{is_script_separator_char, is_symbol_char},
    metamodel::*,
    parenthesis_matcher::*,
    tokenizer::*,
};

// `ParameterEvent` serializes `ParamToken` (defined in tests below) into events.
#[derive(Clone, PartialEq, Debug)]
pub enum ParameterEvent<'a> {
    MetaModel(MetaModelRef),
    ParamGroup(GroupEvent),
    ParamNotation(NotationExpression<'a>),
    Object(GroupEvent),
    Token(TokenEvent<'a>),
}

impl Event for ParameterEvent<'_> {}

#[derive(Clone, PartialEq, Debug)]
pub enum NotationExpression<'a> {
    ReservedChar(char),
    Identifier(Cow<'a, str>),
    Sequence(Vec<NotationExpression<'a>>),
    Paren(char, Vec<NotationExpression<'a>>),
    Param(u32),
}

impl<'a> NotationExpression<'a> {
    fn find_in(&self, parameterizations: &Vec<Self>) -> Option<u32> {
        let mut index = 0;
        for param in parameterizations {
            if *self == *param {
                return Some(index);
            }
            index += 1;
        }
        None
    }

    fn identify(self, parameterizations: &Vec<Self>) -> Self {
        if let Some(index) = self.find_in(parameterizations) {
            NotationExpression::Param(index)
        } else {
            self
        }
    }
}

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
        source: EventSourceWithOps<'a, Self::In, Src>,
    ) -> Self::Pass<Src> {
        ParameterIdentifierPass {
            metamodel_getter: self.metamodel_getter.clone(),
            source,
        }
    }
}

pub struct ParameterIdentifierPass<'a, Src: EventSource + 'a> {
    metamodel_getter: Rc<dyn MetaModelGetter>,
    source: EventSourceWithOps<'a, TokenEvent<'a>, Src>,
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
        self.token_event(state, Some(event), range, &mut out)
    }

    fn next_pass(
        self,
        mut state: Self::State,
        end_marker: &Self::Marker,
        mut out: impl FnMut(Self::Out, Range<&Self::Marker>),
    ) -> Option<Self::NextPass> {
        self.token_event(&mut state, None, end_marker..end_marker, &mut out);
        None
    }
}

// Consumes and outputs the event if it is part of an inner group or parameterization. Otherwise
// returns the event again, so that the client can decide to just output it, or to end the
// expression and then process it.
impl<'a, Src: EventSource + 'a> ParameterIdentifierPass<'a, Src> {
    fn token_event(
        &self,
        state: &mut ParameterIdentifierState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
    ) {
        match &state.metamodel_state {
            MetaModelState::Start => {
                if let Some(TokenEvent::Token(Token::Keyword(keyword))) = event {
                    if keyword == "%slate" {
                        state.metamodel_state = MetaModelState::AfterKeyword;
                    } else {
                        self.source.diagnostic(
                            range,
                            Severity::Error,
                            format!("keyword '%slate' expected"),
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
                if let Some(TokenEvent::Token(Token::DoubleQuotedString(name))) = event {
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
                if matches!(
                    event,
                    None | Some(TokenEvent::Token(Token::ReservedChar(';', _, _)))
                ) {
                    if event.is_none() {
                        self.source.diagnostic(
                            &name_range.end..&name_range.end,
                            Severity::Warning,
                            format!("metamodel reference should be terminated with ';'"),
                        );
                    }
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
                    self.source.diagnostic(
                        &name_range.end..&name_range.end,
                        Severity::Error,
                        format!("';' expected"),
                    );
                    state.metamodel_state = MetaModelState::Failed;
                }
            }

            MetaModelState::Succeeded(metamodel) => {
                self.parameter_list_event(
                    &mut state.list_state,
                    event,
                    range,
                    out,
                    None,
                    metamodel.0.as_ref(),
                    true,
                );
            }

            MetaModelState::Failed => {}
        }
    }

    fn expression_event<'b>(
        &self,
        state: &mut ExpressionState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        metamodel: &dyn MetaModel,
        allow_parameterization: bool,
        allow_objects: bool,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        match state {
            ExpressionState::Start => {
                if allow_parameterization {
                    if let Some(TokenEvent::Paren(GroupEvent::Start(paren))) = event {
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
                if let Some(_) = self.parameter_list_event(
                    list_state.as_mut(),
                    event,
                    range,
                    out,
                    None,
                    metamodel,
                    false,
                ) {
                    *state = ExpressionState::Start;
                }
                None
            }

            ExpressionState::TopLevel { after_dot } => {
                if let Some(TokenEvent::Paren(GroupEvent::Start(paren))) = event {
                    if allow_objects && !*after_dot {
                        if let Some(object) = metamodel.object(paren) {
                            out(ParameterEvent::Object(GroupEvent::Start(())), range);
                            *state = ExpressionState::Object(Box::new(ParameterListState::new(
                                object.param_delimiter(),
                            )));
                            return None;
                        }
                    }
                    out(ParameterEvent::Token(event.unwrap()), range);
                    *state = ExpressionState::Group(Box::new(ExpressionState::Start));
                    None
                } else {
                    *after_dot = false;
                    if let Some(TokenEvent::Token(Token::ReservedChar(c, _, _))) = event {
                        if c == ',' || c == ';' {
                            *state = ExpressionState::Start;
                        } else if c == '.' {
                            *after_dot = true;
                        }
                    } else if event.is_none() {
                        *state = ExpressionState::Start;
                    }
                    Some((event, range))
                }
            }

            ExpressionState::Group(group) => {
                if let Some((event, range)) =
                    self.expression_event(group, event, range, out, metamodel, true, allow_objects)
                {
                    if matches!(event, None | Some(TokenEvent::Paren(GroupEvent::End))) {
                        *state = ExpressionState::TopLevel { after_dot: false };
                    }
                    if let Some(event) = event {
                        out(ParameterEvent::Token(event), range);
                    }
                }
                None
            }

            ExpressionState::Object(list_state) => {
                if let Some(range) = self.parameter_list_event(
                    list_state.as_mut(),
                    event,
                    range,
                    out,
                    None,
                    metamodel,
                    false,
                ) {
                    *state = ExpressionState::TopLevel { after_dot: false };
                    out(ParameterEvent::Object(GroupEvent::End), range);
                }
                None
            }
        }
    }

    fn parameter_list_event<'b>(
        &self,
        state: &mut ParameterListState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        result_notations: Option<&mut Vec<NotationExpression<'a>>>,
        metamodel: &dyn MetaModel,
        top_level: bool,
    ) -> Option<Range<&'b Src::Marker>> {
        let is_group_end = matches!(event, None | Some(TokenEvent::Paren(GroupEvent::End)));

        if let Some(expr_state) = &mut state.after_special_delimiter {
            if let Some((event, range)) =
                self.expression_event(expr_state, event, range, out, metamodel, false, true)
            {
                if is_group_end {
                    return Some(range);
                }
                if let Some(event) = event {
                    out(ParameterEvent::Token(event), range);
                }
            }
        } else {
            let is_special_delimiter = matches!(event, Some(TokenEvent::Token(Token::ReservedChar(c, _, _))) if Some(c) == state.special_delimiter);

            if let Some(group_state) = &mut state.current_group {
                if let Some(range) = self.parameter_group_event(
                    group_state,
                    event,
                    range,
                    out,
                    result_notations,
                    metamodel,
                ) {
                    let group_state = state.current_group.take().unwrap();
                    let current_end = group_state.current_end;
                    out(
                        ParameterEvent::ParamGroup(GroupEvent::End),
                        &current_end..&current_end,
                    );
                    if is_group_end {
                        if top_level {
                            self.source.diagnostic(
                                &current_end..&current_end,
                                Severity::Warning,
                                format!("top-level item should be terminated with ';'"),
                            );
                        }
                        return Some(range);
                    }
                    if is_special_delimiter {
                        state.after_special_delimiter = Some(ExpressionState::Start);
                    }
                }
            } else {
                if is_group_end {
                    return Some(range);
                }
                if is_special_delimiter {
                    state.after_special_delimiter = Some(ExpressionState::Start);
                } else {
                    state.current_group = Some(ParameterGroupState {
                        special_delimiter: state.special_delimiter,
                        current_end: range.start.clone(),
                        parameterizations: Vec::new(),
                        content_state: ParameterGroupContentState::Start,
                    });
                    out(
                        ParameterEvent::ParamGroup(GroupEvent::Start(())),
                        range.start..range.start,
                    );
                    return self.parameter_list_event(
                        state,
                        event,
                        range,
                        out,
                        result_notations,
                        metamodel,
                        top_level,
                    );
                }
            }
        }

        None
    }

    fn parameter_group_event<'b>(
        &self,
        state: &mut ParameterGroupState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        mut result_notations: Option<&mut Vec<NotationExpression<'a>>>,
        metamodel: &dyn MetaModel,
    ) -> Option<Range<&'b Src::Marker>> {
        match &mut state.content_state {
            ParameterGroupContentState::Start => {
                match event {
                    Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                        if c == ';' || Some(c) == state.special_delimiter =>
                    {
                        return Some(range);
                    }
                    Some(TokenEvent::Paren(GroupEvent::Start(paren))) => {
                        if let Some(_) = metamodel.parameterization(paren) {
                            state.content_state = ParameterGroupContentState::Parameterization(
                                Box::new(ParameterListState::new(None)),
                            );
                            return None;
                        }
                    }
                    _ => {}
                }
                state.content_state = ParameterGroupContentState::Notation(None);
                return self.parameter_group_event(
                    state,
                    event,
                    range,
                    out,
                    result_notations,
                    metamodel,
                );
            }

            ParameterGroupContentState::Parameterization(list_state) => {
                if let Some(range) = self.parameter_list_event(
                    list_state.as_mut(),
                    event,
                    range,
                    out,
                    Some(&mut state.parameterizations),
                    metamodel,
                    false,
                ) {
                    state.content_state = ParameterGroupContentState::Start;
                    state.current_end = range.end.clone();
                }
            }

            ParameterGroupContentState::Notation(opt_notation_state) => {
                if opt_notation_state.is_none() {
                    *opt_notation_state = Some(Box::new(NotationExpressionState {
                        notation_start: range.start.clone(),
                        current_end: range.start.clone(),
                        previous_items: Vec::new(),
                        current_item: NotationExpressionItemState::Start,
                    }));
                }
                let notation_state = opt_notation_state.as_mut().unwrap().as_mut();
                if let Some((event, range)) = self.notation_expression_event(
                    notation_state,
                    &state.parameterizations,
                    event,
                    range,
                    metamodel,
                ) {
                    state.current_end = notation_state.current_end.clone();
                    if let Some(notation) = notation_state.extract_notation() {
                        if notation.find_in(&state.parameterizations).is_some() {
                            self.source.diagnostic(
                                &notation_state.notation_start..&state.current_end,
                                Severity::Error,
                                format!("notation cannot match one of its parameters"),
                            );
                        }
                        if let Some(result_notations) = result_notations.as_mut() {
                            result_notations.push(notation.clone());
                        }
                        out(
                            ParameterEvent::ParamNotation(notation),
                            &notation_state.notation_start..&state.current_end,
                        );
                    } else {
                        self.source.diagnostic(
                            range.start..range.start,
                            Severity::Error,
                            format!("parameter expected"),
                        );
                    }
                    match event {
                        None | Some(TokenEvent::Paren(GroupEvent::End)) => {
                            return Some(range);
                        }
                        Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                            if c == ';' || Some(c) == state.special_delimiter =>
                        {
                            return Some(range);
                        }
                        Some(TokenEvent::Token(Token::ReservedChar(',', _, _))) => {
                            *opt_notation_state = None;
                        }
                        _ => {
                            state.content_state =
                                ParameterGroupContentState::Data(ExpressionState::Start);
                            return self.parameter_group_event(
                                state,
                                event,
                                range,
                                out,
                                result_notations,
                                metamodel,
                            );
                        }
                    }
                }
            }

            ParameterGroupContentState::Data(expr_state) => {
                if let Some((event, range)) =
                    self.expression_event(expr_state, event, range, out, metamodel, false, true)
                {
                    match event {
                        None | Some(TokenEvent::Paren(GroupEvent::End)) => {
                            return Some(range);
                        }
                        Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                            if c == ';' || Some(c) == state.special_delimiter =>
                        {
                            return Some(range);
                        }
                        Some(event) => {
                            state.current_end = range.end.clone();
                            out(ParameterEvent::Token(event), range);
                        }
                    }
                }
            }
        }

        None
    }

    fn notation_expression_event<'b>(
        &self,
        state: &mut NotationExpressionState<'a, Src::Marker>,
        parameterizations: &Vec<NotationExpression<'a>>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        metamodel: &dyn MetaModel,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        match &mut state.current_item {
            NotationExpressionItemState::Start => match event {
                Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                    if is_script_separator_char(c) =>
                {
                    state
                        .previous_items
                        .push(NotationExpression::ReservedChar(c));
                    state.current_end = range.end.clone();
                }
                Some(TokenEvent::Token(Token::Identifier(identifier, identifier_type)))
                    if !(identifier_type == IdentifierType::Unquoted
                        && metamodel.is_definition_symbol(&identifier)) =>
                {
                    state.previous_items.push(
                        NotationExpression::Identifier(identifier).identify(parameterizations),
                    );
                    state.current_end = range.end.clone();
                }
                Some(TokenEvent::Paren(GroupEvent::Start(paren))) => {
                    state.current_item = NotationExpressionItemState::Paren(
                        paren,
                        Box::new(NotationExpressionListState {
                            previous_items: Vec::new(),
                            current_item: NotationExpressionListItemState::Start,
                            parameterizations: None,
                        }),
                    );
                }
                _ => {
                    return Some((event, range));
                }
            },

            NotationExpressionItemState::Paren(paren, list_state) => {
                let end_marker = range.end;
                if let Some((event, _)) = self.notation_expression_list_event(
                    list_state.as_mut(),
                    parameterizations,
                    event,
                    range,
                    metamodel,
                ) {
                    if matches!(event, None | Some(TokenEvent::Paren(GroupEvent::End))) {
                        state.previous_items.push(
                            NotationExpression::Paren(*paren, take(&mut list_state.previous_items))
                                .identify(parameterizations),
                        );
                        state.current_item = NotationExpressionItemState::Start;
                        state.current_end = end_marker.clone();
                    }
                }
            }
        }

        None
    }

    fn notation_expression_list_event<'b>(
        &self,
        state: &mut NotationExpressionListState<'a, Src::Marker>,
        parameterizations: &Vec<NotationExpression<'a>>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        metamodel: &dyn MetaModel,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        match &mut state.current_item {
            NotationExpressionListItemState::Start => {
                match event {
                    Some(TokenEvent::Paren(GroupEvent::End)) => {
                        if state.parameterizations.is_some() {
                            self.source.diagnostic(
                                &range.start..&range.start,
                                Severity::Error,
                                format!("parameter reference expected"),
                            );
                        }
                        return Some((event, range));
                    }
                    Some(TokenEvent::Token(Token::ReservedChar(',', _, _))) => {
                        if state.parameterizations.is_some() {
                            self.source.diagnostic(
                                &range.start..&range.start,
                                Severity::Error,
                                format!("parameter reference expected"),
                            );
                            state.parameterizations = None;
                        } else {
                            self.source.diagnostic(
                                range,
                                Severity::Error,
                                format!("superfluous comma"),
                            );
                        }
                        return None;
                    }
                    Some(TokenEvent::Paren(GroupEvent::Start(paren))) => {
                        if let Some(_) = metamodel.parameterization(paren) {
                            if state.parameterizations.is_none() {
                                state.parameterizations = Some(Vec::new());
                            }
                            state.current_item = NotationExpressionListItemState::Parameterization(
                                Box::new(ParameterListState::new(None)),
                            );
                            return None;
                        }
                    }
                    _ => {}
                }
                state.current_item =
                    NotationExpressionListItemState::Notation(Box::new(NotationExpressionState {
                        notation_start: range.start.clone(),
                        current_end: range.start.clone(),
                        previous_items: Vec::new(),
                        current_item: NotationExpressionItemState::Start,
                    }));
                return self.notation_expression_list_event(
                    state,
                    parameterizations,
                    event,
                    range,
                    metamodel,
                );
            }

            NotationExpressionListItemState::Parameterization(list_state) => {
                if let Some(_) = self.parameter_list_event(
                    list_state.as_mut(),
                    event,
                    range,
                    &mut |_, _| {},
                    Some(state.parameterizations.as_mut().unwrap()),
                    metamodel,
                    false,
                ) {
                    state.current_item = NotationExpressionListItemState::Start;
                }
            }

            NotationExpressionListItemState::Notation(notation_state) => {
                if let Some((event, range)) = self.notation_expression_event(
                    notation_state.as_mut(),
                    state
                        .parameterizations
                        .as_ref()
                        .unwrap_or(parameterizations),
                    event,
                    range,
                    metamodel,
                ) {
                    if let Some(notation) = notation_state.extract_notation() {
                        let notation = notation.identify(parameterizations);
                        if state.parameterizations.is_some() {
                            if let NotationExpression::Param(param) = notation {
                                // TODO: compare parameterization
                            } else {
                                self.source.diagnostic(
                                    &notation_state.notation_start..&notation_state.current_end,
                                    Severity::Error,
                                    format!("parameterized expression must match a parameter"),
                                );
                            }
                        }
                        state.previous_items.push(notation);
                    }
                    match event {
                        None | Some(TokenEvent::Paren(GroupEvent::End)) => {
                            return Some((event, range));
                        }
                        Some(TokenEvent::Token(Token::ReservedChar(',', _, _))) => {
                            state.current_item = NotationExpressionListItemState::Start;
                            state.parameterizations = None;
                        }
                        _ => self.source.diagnostic(
                            range,
                            Severity::Error,
                            format!("token not allowed in notation"),
                        ),
                    }
                }
            }
        }

        None
    }
}

#[derive(Clone, PartialEq)]
pub struct ParameterIdentifierState<'a, Marker: Clone + PartialEq> {
    metamodel_state: MetaModelState<'a, Marker>,
    list_state: ParameterListState<'a, Marker>,
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
enum ExpressionState<'a, Marker: Clone + PartialEq> {
    Start,
    Parameterization(Box<ParameterListState<'a, Marker>>),
    TopLevel { after_dot: bool },
    Group(Box<ExpressionState<'a, Marker>>),
    Object(Box<ParameterListState<'a, Marker>>),
}

#[derive(Clone, PartialEq)]
struct ParameterListState<'a, Marker: Clone + PartialEq> {
    special_delimiter: Option<char>,
    current_group: Option<ParameterGroupState<'a, Marker>>,
    after_special_delimiter: Option<ExpressionState<'a, Marker>>,
}

impl<Marker: Clone + PartialEq> ParameterListState<'_, Marker> {
    fn new(special_delimiter: Option<char>) -> Self {
        ParameterListState {
            special_delimiter,
            current_group: None,
            after_special_delimiter: None,
        }
    }
}

#[derive(Clone, PartialEq)]
struct ParameterGroupState<'a, Marker: Clone + PartialEq> {
    special_delimiter: Option<char>,
    current_end: Marker,
    parameterizations: Vec<NotationExpression<'a>>,
    content_state: ParameterGroupContentState<'a, Marker>,
}

#[derive(Clone, PartialEq)]
enum ParameterGroupContentState<'a, Marker: Clone + PartialEq> {
    Start,
    Parameterization(Box<ParameterListState<'a, Marker>>),
    Notation(Option<Box<NotationExpressionState<'a, Marker>>>),
    Data(ExpressionState<'a, Marker>),
}

#[derive(Clone, PartialEq)]
struct NotationExpressionState<'a, Marker: Clone + PartialEq> {
    notation_start: Marker,
    current_end: Marker,
    previous_items: Vec<NotationExpression<'a>>,
    current_item: NotationExpressionItemState<'a, Marker>,
}

impl<'a, Marker: Clone + PartialEq> NotationExpressionState<'a, Marker> {
    fn extract_notation(&mut self) -> Option<NotationExpression<'a>> {
        match self.previous_items.len() {
            0 => None,
            1 => Some(self.previous_items.pop().unwrap()),
            _ => Some(NotationExpression::Sequence(take(&mut self.previous_items))),
        }
    }
}

#[derive(Clone, PartialEq)]
enum NotationExpressionItemState<'a, Marker: Clone + PartialEq> {
    Start,
    Paren(char, Box<NotationExpressionListState<'a, Marker>>),
}

#[derive(Clone, PartialEq)]
struct NotationExpressionListState<'a, Marker: Clone + PartialEq> {
    previous_items: Vec<NotationExpression<'a>>,
    current_item: NotationExpressionListItemState<'a, Marker>,
    parameterizations: Option<Vec<NotationExpression<'a>>>,
}

#[derive(Clone, PartialEq)]
enum NotationExpressionListItemState<'a, Marker: Clone + PartialEq> {
    Start,
    Parameterization(Box<ParameterListState<'a, Marker>>),
    Notation(Box<NotationExpressionState<'a, Marker>>),
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
                        notation: NotationExpression::Identifier("x".into()),
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
                            notation: NotationExpression::Identifier("x".into()),
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
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
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
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("y".into(), IdentifierType::Unquoted)),
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
                            notation: NotationExpression::Identifier("x".into()),
                        }],
                        data: vec![
                            ParamToken::Token(Token::Identifier(
                                ":".into(),
                                IdentifierType::Unquoted,
                            )),
                            ParamToken::Token(Token::Identifier(
                                "T".into(),
                                IdentifierType::Unquoted,
                            )),
                        ],
                    },
                    ParameterGroup {
                        parameterizations: Vec::new(),
                        params: vec![Parameter {
                            notation: NotationExpression::Identifier("y".into()),
                        }],
                        data: vec![
                            ParamToken::Token(Token::Identifier(
                                ":".into(),
                                IdentifierType::Unquoted,
                            )),
                            ParamToken::Token(Token::Identifier(
                                "U".into(),
                                IdentifierType::Unquoted,
                            )),
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
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Identifier("y".into()),
                        ]),
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
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Identifier("y".into()),
                        ]),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Keyword("%z".into())),
                        ParamToken::Paren(
                            '(',
                            vec![
                                ParamToken::Token(Token::Identifier(
                                    "a".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParamToken::Token(Token::ReservedChar(
                                    ';',
                                    TokenIsolation::StronglyConnected,
                                    TokenIsolation::StronglyConnected,
                                )),
                                ParamToken::Token(Token::Identifier(
                                    "b".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x();",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren('(', Vec::new()),
                        ]),
                    }],
                    data: Vec::new(),
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(,);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren('(', Vec::new()),
                        ]),
                    }],
                    data: Vec::new(),
                }],
            },
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y,z);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![
                                    NotationExpression::Identifier("y".into()),
                                    NotationExpression::Identifier("z".into()),
                                ],
                            ),
                        ]),
                    }],
                    data: Vec::new(),
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y,z,);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![
                                    NotationExpression::Identifier("y".into()),
                                    NotationExpression::Identifier("z".into()),
                                ],
                            ),
                        ]),
                    }],
                    data: Vec::new(),
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(,y,z,);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![
                                    NotationExpression::Identifier("y".into()),
                                    NotationExpression::Identifier("z".into()),
                                ],
                            ),
                        ]),
                    }],
                    data: Vec::new(),
                }],
            },
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y,,z,);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![
                                    NotationExpression::Identifier("y".into()),
                                    NotationExpression::Identifier("z".into()),
                                ],
                            ),
                        ]),
                    }],
                    data: Vec::new(),
                }],
            },
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y,z,,);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![
                                    NotationExpression::Identifier("y".into()),
                                    NotationExpression::Identifier("z".into()),
                                ],
                            ),
                        ]),
                    }],
                    data: Vec::new(),
                }],
            },
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y;z);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![
                                    NotationExpression::Identifier("y".into()),
                                    NotationExpression::Identifier("z".into()),
                                ],
                            ),
                        ]),
                    }],
                    data: Vec::new(),
                }],
            },
            &[TestDiagnosticMessage {
                range_text: ";".into(),
                severity: Severity::Error,
                msg: "token not allowed in notation".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(42);",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren('(', Vec::new()),
                        ]),
                    }],
                    data: Vec::new(),
                }],
            },
            &[TestDiagnosticMessage {
                range_text: "42".into(),
                severity: Severity::Error,
                msg: "token not allowed in notation".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x,y;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![
                        Parameter {
                            notation: NotationExpression::Identifier("x".into()),
                        },
                        Parameter {
                            notation: NotationExpression::Identifier("y".into()),
                        },
                    ],
                    data: Vec::new(),
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x,,y : T;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![
                        Parameter {
                            notation: NotationExpression::Identifier("x".into()),
                        },
                        Parameter {
                            notation: NotationExpression::Identifier("y".into()),
                        },
                    ],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                    ],
                }],
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "parameter expected".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x,y : T;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![
                        Parameter {
                            notation: NotationExpression::Identifier("x".into()),
                        },
                        Parameter {
                            notation: NotationExpression::Identifier("y".into()),
                        },
                    ],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; 42;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: Vec::new(),
                    data: vec![ParamToken::Token(Token::Number("42".into()))],
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
                            notation: NotationExpression::Identifier("b".into()),
                        }],
                        data: vec![
                            ParamToken::Token(Token::Identifier(
                                ":".into(),
                                IdentifierType::Unquoted,
                            )),
                            ParamToken::Token(Token::Identifier(
                                "B".into(),
                                IdentifierType::Unquoted,
                            )),
                        ],
                    }],
                    params: vec![Parameter {
                        notation: NotationExpression::Identifier("a".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [b : B] a(b) : A;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: vec![ParameterGroup {
                        parameterizations: Vec::new(),
                        params: vec![Parameter {
                            notation: NotationExpression::Identifier("b".into()),
                        }],
                        data: vec![
                            ParamToken::Token(Token::Identifier(
                                ":".into(),
                                IdentifierType::Unquoted,
                            )),
                            ParamToken::Token(Token::Identifier(
                                "B".into(),
                                IdentifierType::Unquoted,
                            )),
                        ],
                    }],
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("a".into()),
                            NotationExpression::Paren('(', vec![NotationExpression::Param(0)]),
                        ]),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
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
                                notation: NotationExpression::Identifier("d".into()),
                            }],
                            data: vec![
                                ParamToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParamToken::Token(Token::Identifier(
                                    "D".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        }],
                        params: vec![
                            Parameter {
                                notation: NotationExpression::Identifier("b".into()),
                            },
                            Parameter {
                                notation: NotationExpression::Identifier("c".into()),
                            },
                        ],
                        data: vec![
                            ParamToken::Token(Token::Identifier(
                                ":".into(),
                                IdentifierType::Unquoted,
                            )),
                            ParamToken::Token(Token::Identifier(
                                "B".into(),
                                IdentifierType::Unquoted,
                            )),
                        ],
                    }],
                    params: vec![Parameter {
                        notation: NotationExpression::Identifier("a".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[d : D] b(d),c(d) : B] a([d] b(d), [d] c(d)) : A;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: vec![ParameterGroup {
                        parameterizations: vec![ParameterGroup {
                            parameterizations: Vec::new(),
                            params: vec![Parameter {
                                notation: NotationExpression::Identifier("d".into()),
                            }],
                            data: vec![
                                ParamToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParamToken::Token(Token::Identifier(
                                    "D".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        }],
                        params: vec![
                            Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0)],
                                    ),
                                ]),
                            },
                            Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("c".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0)],
                                    ),
                                ]),
                            },
                        ],
                        data: vec![
                            ParamToken::Token(Token::Identifier(
                                ":".into(),
                                IdentifierType::Unquoted,
                            )),
                            ParamToken::Token(Token::Identifier(
                                "B".into(),
                                IdentifierType::Unquoted,
                            )),
                        ],
                    }],
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("a".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(0), NotationExpression::Param(1)],
                            ),
                        ]),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[[e : E] d(e) : D] b([e] d(e)),c([e] d(e)) : B] a([[e] d(e)] b([e] d(e)), [[e] d(e)] c([e] d(e))) : A;",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: vec![ParameterGroup {
                        parameterizations: vec![ParameterGroup {
                            parameterizations: vec![ParameterGroup {
                                parameterizations: Vec::new(),
                                params: vec![Parameter {
                                    notation: NotationExpression::Identifier("e".into()),
                                }],
                                data: vec![
                                    ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                                    ParamToken::Token(Token::Identifier("E".into(), IdentifierType::Unquoted)),
                                ],
                            }],
                            params: vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("d".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0)],
                                    ),
                                ]),
                            }],
                            data: vec![
                                ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                                ParamToken::Token(Token::Identifier("D".into(), IdentifierType::Unquoted)),
                            ],
                        }],
                        params: vec![
                            Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0)],
                                    ),
                                ]),
                            },
                            Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("c".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0)],
                                    ),
                                ]),
                            },
                        ],
                        data: vec![
                            ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                            ParamToken::Token(Token::Identifier("B".into(), IdentifierType::Unquoted)),
                        ],
                    }],
                    params: vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("a".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(0), NotationExpression::Param(1)],
                            ),
                        ]),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
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
                        notation: NotationExpression::Identifier("a".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("f".into(), IdentifierType::Unquoted)),
                        ParamToken::Paren(
                            '(',
                            vec![
                                ParamToken::ParamGroup(ParameterGroup {
                                    parameterizations: Vec::new(),
                                    params: vec![Parameter {
                                        notation: NotationExpression::Identifier("b".into()),
                                    }],
                                    data: vec![
                                        ParamToken::Token(Token::Identifier(
                                            ":".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        ParamToken::Token(Token::Identifier(
                                            "B".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                }),
                                ParamToken::Token(Token::Identifier(
                                    "b".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    ],
                }],
            },
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; a := f[[b : B] b, [[d : D] ⟦e,f : E⟧ c[d,f] : C] c[0,1]];",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Identifier("a".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("f".into(), IdentifierType::Unquoted)),
                        ParamToken::Paren(
                            '[',
                            vec![
                                ParamToken::ParamGroup(ParameterGroup {
                                    parameterizations: Vec::new(),
                                    params: vec![Parameter {
                                        notation: NotationExpression::Identifier("b".into()),
                                    }],
                                    data: vec![
                                        ParamToken::Token(Token::Identifier(
                                            ":".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        ParamToken::Token(Token::Identifier(
                                            "B".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                }),
                                ParamToken::Token(Token::Identifier(
                                    "b".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParamToken::Token(Token::ReservedChar(
                                    ',',
                                    TokenIsolation::StronglyConnected,
                                    TokenIsolation::Isolated,
                                )),
                                ParamToken::ParamGroup(ParameterGroup {
                                    parameterizations: vec![
                                        ParameterGroup {
                                            parameterizations: Vec::new(),
                                            params: vec![Parameter {
                                                notation: NotationExpression::Identifier(
                                                    "d".into(),
                                                ),
                                            }],
                                            data: vec![
                                                ParamToken::Token(Token::Identifier(
                                                    ":".into(),
                                                    IdentifierType::Unquoted,
                                                )),
                                                ParamToken::Token(Token::Identifier(
                                                    "D".into(),
                                                    IdentifierType::Unquoted,
                                                )),
                                            ],
                                        },
                                        ParameterGroup {
                                            parameterizations: Vec::new(),
                                            params: vec![
                                                Parameter {
                                                    notation: NotationExpression::Identifier(
                                                        "e".into(),
                                                    ),
                                                },
                                                Parameter {
                                                    notation: NotationExpression::Identifier(
                                                        "f".into(),
                                                    ),
                                                },
                                            ],
                                            data: vec![
                                                ParamToken::Token(Token::Identifier(
                                                    ":".into(),
                                                    IdentifierType::Unquoted,
                                                )),
                                                ParamToken::Token(Token::Identifier(
                                                    "E".into(),
                                                    IdentifierType::Unquoted,
                                                )),
                                            ],
                                        },
                                    ],
                                    params: vec![Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("c".into()),
                                            NotationExpression::Paren(
                                                '[',
                                                vec![
                                                    NotationExpression::Param(0),
                                                    NotationExpression::Param(2),
                                                ],
                                            ),
                                        ]),
                                    }],
                                    data: vec![
                                        ParamToken::Token(Token::Identifier(
                                            ":".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        ParamToken::Token(Token::Identifier(
                                            "C".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                }),
                                ParamToken::Token(Token::Identifier(
                                    "c".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParamToken::Paren(
                                    '[',
                                    vec![
                                        ParamToken::Token(Token::Number("0".into())),
                                        ParamToken::Token(Token::ReservedChar(
                                            ',',
                                            TokenIsolation::StronglyConnected,
                                            TokenIsolation::StronglyConnected,
                                        )),
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
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
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
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        ParamToken::Object(
                            vec![ParameterGroup {
                                parameterizations: Vec::new(),
                                params: vec![Parameter {
                                    notation: NotationExpression::Identifier("x".into()),
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
            "%slate \"test\"; T := { | x};",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        ParamToken::Object(
                            Vec::new(),
                            vec![ParamToken::Token(Token::Identifier(
                                "x".into(),
                                IdentifierType::Unquoted,
                            ))],
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
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        ParamToken::Object(
                            vec![
                                ParameterGroup {
                                    parameterizations: vec![ParameterGroup {
                                        parameterizations: Vec::new(),
                                        params: vec![Parameter {
                                            notation: NotationExpression::Identifier("i".into()),
                                        }],
                                        data: vec![
                                            ParamToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            ParamToken::Token(Token::Identifier(
                                                "I".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    }],
                                    params: vec![
                                        Parameter {
                                            notation: NotationExpression::Identifier("x".into()),
                                        },
                                        Parameter {
                                            notation: NotationExpression::Identifier("x'".into()),
                                        },
                                    ],
                                    data: vec![
                                        ParamToken::Token(Token::Identifier(
                                            ":".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        ParamToken::Token(Token::Identifier(
                                            "X".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                },
                                ParameterGroup {
                                    parameterizations: vec![ParameterGroup {
                                        parameterizations: Vec::new(),
                                        params: vec![Parameter {
                                            notation: NotationExpression::Identifier("j".into()),
                                        }],
                                        data: vec![
                                            ParamToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            ParamToken::Token(Token::Identifier(
                                                "J".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    }],
                                    params: vec![
                                        Parameter {
                                            notation: NotationExpression::Identifier("y".into()),
                                        },
                                        Parameter {
                                            notation: NotationExpression::Identifier("y'".into()),
                                        },
                                    ],
                                    data: vec![
                                        ParamToken::Token(Token::Identifier(
                                            ":".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        ParamToken::Token(Token::Identifier(
                                            "Y".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                },
                            ],
                            vec![
                                ParamToken::Token(Token::Identifier(
                                    "a".into(),
                                    IdentifierType::Unquoted,
                                )),
                                ParamToken::Token(Token::ReservedChar(
                                    '|',
                                    TokenIsolation::Isolated,
                                    TokenIsolation::Isolated,
                                )),
                                ParamToken::Token(Token::Identifier(
                                    "b".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                        ParamToken::Token(Token::ReservedChar(
                            '|',
                            TokenIsolation::Isolated,
                            TokenIsolation::Isolated,
                        )),
                        ParamToken::Object(
                            vec![ParameterGroup {
                                parameterizations: Vec::new(),
                                params: vec![Parameter {
                                    notation: NotationExpression::Identifier("z".into()),
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
            "%slate \"test\"; ℕ := {@\"0\"; [n : ℕ] S(n)};",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Identifier("ℕ".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        ParamToken::Object(
                            vec![
                                ParameterGroup {
                                    parameterizations: Vec::new(),
                                    params: vec![Parameter {
                                        notation: NotationExpression::Identifier("0".into()),
                                    }],
                                    data: Vec::new(),
                                },
                                ParameterGroup {
                                    parameterizations: vec![ParameterGroup {
                                        parameterizations: Vec::new(),
                                        params: vec![Parameter {
                                            notation: NotationExpression::Identifier("n".into()),
                                        }],
                                        data: vec![
                                            ParamToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            ParamToken::Token(Token::Identifier(
                                                "ℕ".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    }],
                                    params: vec![Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("S".into()),
                                            NotationExpression::Paren(
                                                '(',
                                                vec![NotationExpression::Param(0)],
                                            ),
                                        ]),
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
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::ReservedChar(
                            '.',
                            TokenIsolation::StronglyConnected,
                            TokenIsolation::StronglyConnected,
                        )),
                        ParamToken::Paren(
                            '{',
                            vec![ParamToken::Token(Token::Identifier(
                                "t".into(),
                                IdentifierType::Unquoted,
                            ))],
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
                msg: "metamodel reference expected".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: Vec::new(),
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Warning,
                msg: "metamodel reference should be terminated with ';'".into(),
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
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    data: Vec::new(),
                }],
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Warning,
                msg: "top-level item should be terminated with ';'".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x : T",
            Document {
                metamodel: Some(TestMetaModel::new_ref()),
                definitions: vec![ParameterGroup {
                    parameterizations: Vec::new(),
                    params: vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    data: vec![
                        ParamToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        ParamToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                    ],
                }],
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Warning,
                msg: "top-level item should be terminated with ';'".into(),
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
            Self::group(
                (),
                result,
                |event| ParameterEvent::ParamGroup(event),
                |result| {
                    self.parameterizations.fill_events(result);
                    self.params.fill_events(result);
                    self.data.fill_events(result);
                },
            );
        }
    }

    struct Parameter<'a> {
        notation: NotationExpression<'a>,
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for Parameter<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            result.push(ParameterEvent::ParamNotation(self.notation));
        }
    }

    enum ParamToken<'a> {
        Token(Token<'a>),
        Paren(char, Vec<ParamToken<'a>>),
        ParamGroup(ParameterGroup<'a>),
        Object(Vec<ParameterGroup<'a>>, Vec<ParamToken<'a>>),
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for ParamToken<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            match self {
                ParamToken::Token(token) => {
                    result.push(ParameterEvent::Token(TokenEvent::Token(token)))
                }
                ParamToken::Paren(paren, contents) => {
                    Self::group(
                        paren,
                        result,
                        |event| ParameterEvent::Token(TokenEvent::Paren(event)),
                        |result| contents.fill_events(result),
                    );
                }
                ParamToken::ParamGroup(param_group) => {
                    param_group.fill_events(result);
                }
                ParamToken::Object(params, data) => {
                    Self::group(
                        (),
                        result,
                        |event| ParameterEvent::Object(event),
                        |result| {
                            params.fill_events(result);
                            data.fill_events(result);
                        },
                    );
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
