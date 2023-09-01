use std::{borrow::Cow, collections::VecDeque, ops::Range};

use slate_kernel_notation_generic::{event::*, event_translator::*};
use slate_kernel_util::queue_slice::*;

use crate::{chars::*, metamodel::*, parenthesis_matcher::*, tokenizer::*};

// `ParameterEvent` serializes `ParamToken` (defined in tests below) into events.
#[derive(Clone, PartialEq, Debug)]
pub enum ParameterEvent<'a> {
    MetaModel(&'a dyn MetaModel),
    SectionItem(GroupEvent),
    Parameterization(GroupEvent<&'a dyn SectionKind>),
    SectionItemBody(GroupEvent<SectionItemType<'a>>),
    ParamNotation(NotationExpression<'a>),
    Token(TokenEvent<'a>),
    SpecialData(GroupEvent<&'a dyn DataKind>),
    Mapping(GroupEvent<&'a dyn MappingKind>),
    MappingParam(GroupEvent),
    Object(GroupEvent<&'a dyn ObjectKind>),
    ObjectItem(GroupEvent),
    ObjectItemExtra(GroupEvent),
}

impl Event for ParameterEvent<'_> {}

#[derive(Clone, PartialEq, Debug)]
pub enum SectionItemType<'a> {
    ParamGroup,
    Section(&'a dyn SectionKind),
}

#[derive(Clone, PartialEq, Debug)]
pub enum NotationExpression<'a> {
    ReservedChar(char),
    Identifier(Cow<'a, str>),
    Sequence(Vec<NotationExpression<'a>>),
    Paren(char, Vec<NotationExpression<'a>>),
    Param(u32),
}

impl<'a> NotationExpression<'a> {
    fn find_in(&self, parameterizations: &[&Parameterization<'a>]) -> Option<u32> {
        let mut index = 0;
        for param in parameterizations {
            if *self == param.notation {
                return Some(index);
            }
            index += 1;
        }
        None
    }

    fn identify(self, parameterizations: &[&Parameterization<'a>]) -> Self {
        if let Some(index) = self.find_in(parameterizations) {
            NotationExpression::Param(index)
        } else {
            self
        }
    }
}

pub struct ParameterIdentifier<'a> {
    metamodel_getter: &'a dyn MetaModelGetter,
}

impl<'a> ParameterIdentifier<'a> {
    pub fn new(metamodel_getter: &'a impl MetaModelGetter) -> Self {
        ParameterIdentifier { metamodel_getter }
    }
}

impl<'a> EventTranslator<'a> for ParameterIdentifier<'a> {
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
    metamodel_getter: &'a dyn MetaModelGetter,
    source: EventSourceWithOps<'a, TokenEvent<'a>, Src>,
}

impl<'a, Src: EventSource + 'a> EventTranslatorPass for ParameterIdentifierPass<'a, Src> {
    type In = TokenEvent<'a>;
    type Out = ParameterEvent<'a>;
    type Marker = Src::Marker;
    type State = ParameterIdentifierState<'a, Src::Marker>;

    fn new_state(&self) -> Self::State {
        ParameterIdentifierState::Start
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

impl<'a, Src: EventSource + 'a> ParameterIdentifierPass<'a, Src> {
    fn token_event(
        &self,
        state: &mut ParameterIdentifierState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
    ) {
        match state {
            ParameterIdentifierState::Start => {
                if let Some(TokenEvent::Token(Token::Keyword(keyword))) = event {
                    if keyword == "%slate" {
                        *state = ParameterIdentifierState::AfterKeyword;
                    } else {
                        self.source.diagnostic(
                            range,
                            Severity::Error,
                            format!("keyword '%slate' expected"),
                        );
                        *state = ParameterIdentifierState::MetaModelFailed;
                    }
                } else {
                    self.source.diagnostic(
                        range,
                        Severity::Error,
                        format!("metamodel reference expected"),
                    );
                    *state = ParameterIdentifierState::MetaModelFailed;
                }
            }

            ParameterIdentifierState::AfterKeyword => {
                if let Some(TokenEvent::Token(Token::DoubleQuotedString(name))) = event {
                    *state = ParameterIdentifierState::AfterName {
                        name,
                        name_range: range.start.clone()..range.end.clone(),
                    };
                } else {
                    self.source.diagnostic(
                        range,
                        Severity::Error,
                        format!("metamodel name must be a string"),
                    );
                    *state = ParameterIdentifierState::MetaModelFailed;
                }
            }

            ParameterIdentifierState::AfterName { name, name_range } => {
                if matches!(
                    event,
                    None | Some(TokenEvent::Token(Token::ReservedChar(';', _, _)))
                ) {
                    match self.metamodel_getter.metamodel(name) {
                        Ok(metamodel) => {
                            out(
                                ParameterEvent::MetaModel(metamodel.clone()),
                                &name_range.start..&name_range.end,
                            );
                            *state = ParameterIdentifierState::MetaModelSucceeded {
                                metamodel,
                                section_state: SectionState::Start,
                            };
                        }
                        Err(err) => {
                            self.source.diagnostic(
                                &name_range.start..&name_range.end,
                                Severity::Error,
                                err.to_string(),
                            );
                            *state = ParameterIdentifierState::MetaModelFailed;
                        }
                    }
                } else {
                    self.source.diagnostic(
                        &name_range.end..&name_range.end,
                        Severity::Error,
                        format!("';' expected"),
                    );
                    *state = ParameterIdentifierState::MetaModelFailed;
                }
            }

            ParameterIdentifierState::MetaModelSucceeded {
                metamodel,
                section_state,
            } => {
                let is_end = event.is_none();
                let range = self.section_event(
                    section_state,
                    event,
                    range,
                    out,
                    metamodel.top_level_section_kind(),
                    None,
                    &[],
                    &mut None,
                );
                assert!(range.is_some() == is_end);
            }

            ParameterIdentifierState::MetaModelFailed => {}
        }
    }

    // Returns `Some(range)` if the event ended the section and was not consumed.
    fn section_event<'b>(
        &self,
        state: &mut SectionState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        section_kind: &'a dyn SectionKind,
        separator: Option<char>,
        outer_parameterizations: &[&Parameterization<'a>],
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        match state {
            SectionState::Start => match event {
                Some(TokenEvent::Token(Token::ReservedChar(';', _, _))) => {
                    self.source.diagnostic(
                        range.clone(),
                        Severity::Warning,
                        format!("superfluous semicolon"),
                    );
                    None
                }
                Some(TokenEvent::Token(Token::ReservedChar(c, _, _))) if Some(c) == separator => {
                    Some((event, range))
                }
                Some(TokenEvent::Paren(GroupEvent::End)) | None => Some((event, range)),
                _ => {
                    out(
                        ParameterEvent::SectionItem(GroupEvent::Start(())),
                        range.start..range.start,
                    );
                    *state = SectionState::Item {
                        parameterizations: None,
                        item_state: SectionItemState::Start,
                    };
                    self.section_event(
                        state,
                        event,
                        range,
                        out,
                        section_kind,
                        separator,
                        outer_parameterizations,
                        result_params,
                    )
                }
            },

            SectionState::Item {
                parameterizations,
                item_state,
            } => {
                if let Some((event, range)) = self.section_item_event(
                    parameterizations,
                    item_state,
                    event,
                    range,
                    out,
                    section_kind,
                    separator,
                    outer_parameterizations,
                    result_params,
                ) {
                    *state = SectionState::Start;
                    match event {
                        Some(TokenEvent::Paren(GroupEvent::End)) | None => Some((event, range)),
                        Some(TokenEvent::Token(Token::ReservedChar(';', _, _))) => None,
                        Some(TokenEvent::Token(Token::ReservedChar(',', _, _))) => {
                            self.source.diagnostic(
                                range,
                                Severity::Error,
                                format!("expected semicolon instead of comma"),
                            );
                            None
                        }
                        _ => self.section_event(
                            state,
                            event,
                            range,
                            out,
                            section_kind,
                            separator,
                            outer_parameterizations,
                            result_params,
                        ),
                    }
                } else {
                    None
                }
            }
        }
    }

    fn section_item_event<'b>(
        &self,
        parameterizations: &mut Option<Vec<Parameterization<'a>>>,
        state: &mut SectionItemState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        section_kind: &'a dyn SectionKind,
        separator: Option<char>,
        outer_parameterizations: &[&Parameterization<'a>],
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        match state {
            SectionItemState::Start => {
                let mut item_expected = || {
                    self.source.diagnostic(
                        range.start..range.start,
                        Severity::Error,
                        format!("item expected"),
                    );
                    out(
                        ParameterEvent::SectionItem(GroupEvent::End),
                        range.start..range.start,
                    );
                };

                match event {
                    Some(TokenEvent::Paren(GroupEvent::Start(start_paren))) => {
                        match section_kind.parenthesis_role(start_paren) {
                            SectionParenthesisRole::None => {}
                            SectionParenthesisRole::Parameterization(parameterization_kind) => {
                                out(
                                    ParameterEvent::Parameterization(GroupEvent::Start(
                                        parameterization_kind,
                                    )),
                                    range.clone(),
                                );
                                *state = SectionItemState::Parameterization(
                                    parameterization_kind,
                                    Box::new(SectionState::Start),
                                );
                                return None;
                            }
                            SectionParenthesisRole::Section(section_kind) => {
                                out(
                                    ParameterEvent::SectionItemBody(GroupEvent::Start(
                                        SectionItemType::Section(section_kind),
                                    )),
                                    range.clone(),
                                );
                                *state = SectionItemState::Subsection(
                                    section_kind,
                                    Box::new(SectionState::Start),
                                );
                                return None;
                            }
                        }
                    }
                    Some(TokenEvent::Paren(GroupEvent::End)) | None => {
                        item_expected();
                        return Some((event, range));
                    }
                    Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                        if c == ',' || c == ';' || Some(c) == separator =>
                    {
                        item_expected();
                        return Some((event, range));
                    }
                    _ => {}
                }

                out(
                    ParameterEvent::SectionItemBody(GroupEvent::Start(SectionItemType::ParamGroup)),
                    range.start..range.start,
                );
                *state = SectionItemState::ParamGroup {
                    group_state: ParamGroupState::new(),
                    end_marker: range.start.clone(),
                };
                self.section_item_event(
                    parameterizations,
                    state,
                    event,
                    range,
                    out,
                    section_kind,
                    separator,
                    outer_parameterizations,
                    result_params,
                )
            }

            SectionItemState::Parameterization(parameterization_kind, parameterization_state) => {
                if parameterizations.is_none() {
                    *parameterizations = Some(Vec::new());
                }
                if let Some((_, range)) = self.section_event(
                    parameterization_state,
                    event,
                    range,
                    out,
                    *parameterization_kind,
                    None,
                    &[],
                    parameterizations,
                ) {
                    out(ParameterEvent::Parameterization(GroupEvent::End), range);
                    *state = SectionItemState::Start;
                }
                None
            }

            SectionItemState::ParamGroup {
                group_state,
                end_marker,
            } => {
                let end = range.end;
                if let Some((event, range)) = self.param_group_event(
                    group_state,
                    event,
                    range,
                    out,
                    section_kind.param_kind(),
                    separator,
                    outer_parameterizations,
                    parameterizations.as_deref(),
                    result_params,
                ) {
                    out(
                        ParameterEvent::SectionItemBody(GroupEvent::End),
                        end_marker..end_marker,
                    );
                    out(
                        ParameterEvent::SectionItem(GroupEvent::End),
                        end_marker..end_marker,
                    );
                    Some((event, range))
                } else {
                    *end_marker = end.clone();
                    None
                }
            }

            SectionItemState::Subsection(subsection_kind, subsection_state) => {
                if let Some((_, range)) = self.section_event(
                    subsection_state,
                    event,
                    range,
                    out,
                    *subsection_kind,
                    None,
                    &Parameterization::concat(
                        outer_parameterizations,
                        parameterizations.as_deref(),
                    ),
                    result_params,
                ) {
                    out(
                        ParameterEvent::SectionItemBody(GroupEvent::End),
                        range.clone(),
                    );
                    out(
                        ParameterEvent::SectionItem(GroupEvent::End),
                        range.end..range.end,
                    );
                    *state = SectionItemState::AfterSubsection;
                }
                None
            }

            SectionItemState::AfterSubsection => Some((event, range)),
        }
    }

    fn param_group_event<'b>(
        &self,
        state: &mut ParamGroupState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        separator: Option<char>,
        outer_parameterizations: &[&Parameterization<'a>],
        inner_parameterizations: Option<&[Parameterization<'a>]>,
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        let mut end_segment = |end_group| {
            let mut result = false;
            if state.notation_len > 0 {
                RecordedTokenSlice::new(&mut state.recorded_tokens).with_subslice(
                    state.notation_len,
                    |notation_tokens| {
                        self.output_notation(
                            notation_tokens,
                            out,
                            &Parameterization::concat(
                                outer_parameterizations,
                                inner_parameterizations,
                            ),
                            result_params,
                        );
                        assert!(notation_tokens.is_empty());
                    },
                );
                state.notation_len = 0;
                result = true;
            }
            if end_group {
                self.output_data(
                    &mut RecordedTokenSlice::new(&mut state.recorded_tokens),
                    None,
                    out,
                    param_kind.data_kind(),
                );
                result = true;
            }
            result
        };

        if let Some(event) = event {
            match &event {
                TokenEvent::Token(Token::ReservedChar(',', _, _))
                    if state.paren_depth == 0 && !state.in_data =>
                {
                    if !end_segment(false) {
                        self.source.diagnostic(
                            range,
                            Severity::Error,
                            format!("superfluous comma"),
                        );
                    }
                    return None;
                }
                TokenEvent::Token(Token::ReservedChar('.', _, _))
                | TokenEvent::Token(Token::Keyword(_))
                    if !state.in_data =>
                {
                    end_segment(false);
                    state.in_data = true;
                }
                TokenEvent::Token(Token::ReservedChar(c, _, _))
                    if state.paren_depth == 0
                        && (*c == ',' || *c == ';' || Some(*c) == separator) =>
                {
                    end_segment(true);
                    return Some((Some(event), range));
                }
                TokenEvent::Token(Token::Identifier(identifier, IdentifierType::Unquoted))
                    if !state.in_data =>
                {
                    if param_kind.identifier_is_notation_delimiter(identifier) {
                        end_segment(false);
                        state.in_data = true;
                    }
                    if state.paren_depth == 0 {
                        if let Some(mapping_kind) = param_kind.mapping_kind(identifier) {
                            if matches!(
                                mapping_kind.notation(),
                                MappingNotation::Infix { binder_paren: _ }
                            ) {
                                end_segment(false);
                                state.in_data = true;
                            }
                        }
                    }
                }
                TokenEvent::Paren(GroupEvent::Start(start_paren)) => {
                    if param_kind.paren_is_notation_delimiter(*start_paren) {
                        end_segment(false);
                        state.in_data = true;
                    }
                    state.paren_depth += 1;
                }
                TokenEvent::Paren(GroupEvent::End) => {
                    if state.paren_depth > 0 {
                        state.paren_depth -= 1;
                    } else {
                        end_segment(true);
                        return Some((Some(event), range));
                    }
                }
                _ => {}
            }
            state
                .recorded_tokens
                .push_back((event, range.start.clone()..range.end.clone()));
            if state.paren_depth == 0 && !state.in_data {
                state.notation_len = state.recorded_tokens.len();
            }
            None
        } else {
            end_segment(true);
            Some((None, range))
        }
    }

    fn output_notation(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        parameterizations: &[&Parameterization<'a>],
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> bool {
        if let Some((notation, range)) = self.create_notation_expression(tokens, parameterizations)
        {
            if let Some(result_params) = result_params {
                result_params.push(Parameterization {
                    notation: notation.clone(),
                });
            }
            out(
                ParameterEvent::ParamNotation(notation),
                &range.start..&range.end,
            );
            true
        } else {
            false
        }
    }

    fn create_notation_expression(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        parameterizations: &[&Parameterization<'a>],
    ) -> Option<(NotationExpression<'a>, Range<Src::Marker>)> {
        let mut current_sequence = Vec::new();
        let mut start = None;
        let mut end = None;

        while let Some((event, _)) = tokens.front() {
            if matches!(
                event,
                TokenEvent::Token(Token::ReservedChar(',', _, _))
                    | TokenEvent::Paren(GroupEvent::End)
            ) {
                break;
            }

            let (event, range) = tokens.pop_front().unwrap();

            if start.is_none() {
                start = Some(range.start.clone());
            }

            match event {
                TokenEvent::Token(Token::ReservedChar(c, _, _)) if is_script_separator_char(c) => {
                    current_sequence.push(NotationExpression::ReservedChar(c));
                }
                TokenEvent::Token(Token::Identifier(identifier, _)) => {
                    current_sequence.push(
                        NotationExpression::Identifier(identifier).identify(parameterizations),
                    );
                }
                TokenEvent::Paren(GroupEvent::Start(start_paren)) => {
                    let mut items = Vec::new();
                    loop {
                        let prev_len = tokens.len();
                        if let Some((item, _)) =
                            self.create_notation_expression(tokens, parameterizations)
                        {
                            items.push(item);
                        }
                        let item_read = tokens.len() < prev_len;
                        let (event, range) = tokens.pop_front().unwrap();
                        match event {
                            TokenEvent::Paren(GroupEvent::End) => break,
                            TokenEvent::Token(Token::ReservedChar(',', _, _)) => {
                                if !item_read {
                                    self.source.diagnostic(
                                        &range.start..&range.end,
                                        Severity::Error,
                                        format!("superfluous comma"),
                                    );
                                }
                            }
                            _ => panic!("unexpected end of notation expression"),
                        }
                    }
                    current_sequence.push(NotationExpression::Paren(start_paren, items));
                }
                _ => self.source.diagnostic(
                    &range.start..&range.end,
                    Severity::Error,
                    format!("token not allowed in notation"),
                ),
            }

            end = Some(range.end);
        }

        if current_sequence.is_empty() {
            None
        } else if current_sequence.len() == 1 {
            Some((
                current_sequence.pop().unwrap(),
                start.unwrap()..end.unwrap(),
            ))
        } else {
            Some((
                NotationExpression::Sequence(current_sequence),
                start.unwrap()..end.unwrap(),
            ))
        }
    }

    fn output_data(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        separator: Option<char>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        data_kind: Option<&'a dyn DataKind>,
    ) -> Option<Src::Marker> {
        let get_mapping_kind = |identifier: &str| {
            if let Some(data_kind) = data_kind {
                data_kind.mapping_kind(identifier)
            } else {
                None
            }
        };

        let mut end = None;
        let mut mapping_depth: u32 = 0;

        loop {
            let (content_len, full_len, paren, mapping_kind) =
                self.analyze_data_segment(tokens, separator, get_mapping_kind);

            if let Some(mapping_kind) = mapping_kind {
                if matches!(mapping_kind.notation(), MappingNotation::Prefix) && content_len > 0 {
                    tokens.with_subslice(content_len, |segment_tokens| {
                        self.output_data_segment(segment_tokens, out, data_kind);
                        assert!(segment_tokens.is_empty());
                    });
                }

                let (_, range) = tokens.front().unwrap();
                out(
                    ParameterEvent::Mapping(GroupEvent::Start(mapping_kind)),
                    &range.start..&range.start,
                );
                mapping_depth += 1;

                end = Some(self.output_mapping_source_by_notation(
                    tokens,
                    out,
                    mapping_kind,
                    paren,
                    content_len,
                    get_mapping_kind,
                    &mut None,
                ));
            } else {
                if content_len > 0 {
                    tokens.with_subslice(content_len, |segment_tokens| {
                        end = self.output_data_segment(segment_tokens, out, data_kind);
                        assert!(segment_tokens.is_empty());
                    });
                }

                while mapping_depth > 0 {
                    mapping_depth -= 1;
                    let mapping_end = end.as_ref().unwrap();
                    out(
                        ParameterEvent::Mapping(GroupEvent::End),
                        mapping_end..mapping_end,
                    );
                }

                if full_len > content_len {
                    assert_eq!(full_len, content_len + 1);
                    let (event, range) = tokens.pop_front().unwrap();
                    out(ParameterEvent::Token(event), &range.start..&range.end);
                    end = Some(range.end);
                } else if full_len == 0 {
                    break;
                }
            }
        }

        assert_eq!(mapping_depth, 0);
        end
    }

    fn analyze_data_segment(
        &self,
        tokens: &RecordedTokenSlice<'a, '_, Src::Marker>,
        separator: Option<char>,
        get_mapping_kind: impl Fn(&str) -> Option<&'a dyn MappingKind>,
    ) -> (usize, usize, Option<char>, Option<&'a dyn MappingKind>) {
        let mut paren_depth: u32 = 0;
        let mut end_idx = 0;
        let mut paren = None;

        for (idx, (event, _)) in tokens.iter().enumerate() {
            match event {
                TokenEvent::Token(Token::ReservedChar(c, _, _))
                    if paren_depth == 0 && Some(*c) == separator =>
                {
                    break
                }
                TokenEvent::Paren(GroupEvent::Start(start_paren)) => {
                    if idx == 0 {
                        paren = Some(*start_paren);
                    }
                    paren_depth += 1;
                }
                TokenEvent::Paren(GroupEvent::End) => {
                    if paren_depth > 0 {
                        paren_depth -= 1;
                    } else {
                        break;
                    }
                }
                _ => {}
            }

            end_idx = idx + 1;

            if paren_depth == 0 {
                match event {
                    TokenEvent::Token(Token::ReservedChar(',', _, _))
                    | TokenEvent::Token(Token::ReservedChar(';', _, _)) => {
                        return (idx, end_idx, paren, None);
                    }
                    TokenEvent::Token(Token::Identifier(identifier, IdentifierType::Unquoted)) => {
                        if let Some(mapping_kind) = get_mapping_kind(identifier) {
                            if idx > 0 || matches!(mapping_kind.notation(), MappingNotation::Prefix)
                            {
                                return (idx, end_idx, paren, Some(mapping_kind));
                            }
                        }
                    }
                    _ => {}
                }

                if idx > 0 && !matches!(event, TokenEvent::Paren(GroupEvent::End)) {
                    paren = None;
                }
            }
        }

        (end_idx, end_idx, paren, None)
    }

    fn output_data_segment(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        data_kind: Option<&'a dyn DataKind>,
    ) -> Option<Src::Marker> {
        let mut end = None;

        while let Some((event, range)) = tokens.pop_front() {
            if let TokenEvent::Paren(GroupEvent::Start(start_paren)) = event {
                if let Some(data_kind) = data_kind {
                    if let Some(special_data_kind) = data_kind.special_data_kind(start_paren) {
                        out(
                            ParameterEvent::SpecialData(GroupEvent::Start(special_data_kind)),
                            &range.start..&range.end,
                        );
                        self.output_data(tokens, None, out, Some(special_data_kind));
                        let (event, range) = tokens.pop_front().unwrap();
                        assert_eq!(event, TokenEvent::Paren(GroupEvent::End));
                        out(
                            ParameterEvent::SpecialData(GroupEvent::End),
                            &range.start..&range.end,
                        );
                        end = Some(range.end);
                        continue;
                    }

                    if let Some(object_kind) = data_kind.object_kind(start_paren) {
                        out(
                            ParameterEvent::Object(GroupEvent::Start(object_kind)),
                            &range.start..&range.end,
                        );
                        self.output_object(tokens, out, object_kind);
                        let (event, range) = tokens.pop_front().unwrap();
                        assert_eq!(event, TokenEvent::Paren(GroupEvent::End));
                        out(
                            ParameterEvent::Object(GroupEvent::End),
                            &range.start..&range.end,
                        );
                        end = Some(range.end);
                        continue;
                    }
                }

                out(ParameterEvent::Token(event), &range.start..&range.end);
                self.output_data(tokens, None, out, data_kind);
                let (event, range) = tokens.pop_front().unwrap();
                assert_eq!(event, TokenEvent::Paren(GroupEvent::End));
                out(ParameterEvent::Token(event), &range.start..&range.end);
                end = Some(range.end);
                continue;
            }

            out(ParameterEvent::Token(event), &range.start..&range.end);

            end = Some(range.end);
        }

        end
    }

    fn output_mapping_source_by_notation(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        mapping_kind: &'a dyn MappingKind,
        paren: Option<char>,
        mut source_len: usize,
        get_mapping_kind: impl Fn(&str) -> Option<&'a dyn MappingKind>,
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Src::Marker {
        match mapping_kind.notation() {
            MappingNotation::Prefix => {
                let (event, range) = tokens.pop_front().unwrap();
                assert!(matches!(event,
                                 TokenEvent::Token(Token::Identifier(identifier, IdentifierType::Unquoted))
                                     if get_mapping_kind(&identifier) == Some(mapping_kind)));
                let source_end = self
                    .output_mapping_source(
                        tokens,
                        Some('.'),
                        out,
                        mapping_kind.param_kind(),
                        &[],
                        result_params,
                    )
                    .unwrap_or(range.end);
                if let Some((event, range)) = tokens.pop_front() {
                    assert!(matches!(
                        event,
                        TokenEvent::Token(Token::ReservedChar('.', _, _))
                    ));
                    range.end
                } else {
                    self.source.diagnostic(
                        &source_end..&source_end,
                        Severity::Error,
                        format!("'.' expected"),
                    );
                    source_end
                }
            }

            MappingNotation::Infix { binder_paren } => {
                if paren == Some(binder_paren) {
                    source_len -= 2;
                    let (event, _) = tokens.pop_front().unwrap();
                    assert!(matches!(
                        event,
                        TokenEvent::Paren(GroupEvent::Start(start_paren))
                            if start_paren == binder_paren
                    ));
                }
                tokens.with_subslice(source_len, |source_tokens| {
                    self.output_mapping_source(
                        source_tokens,
                        None,
                        out,
                        mapping_kind.param_kind(),
                        &[],
                        result_params,
                    );
                    assert!(source_tokens.is_empty());
                });
                if paren == Some(binder_paren) {
                    let (event, _) = tokens.pop_front().unwrap();
                    assert!(matches!(event, TokenEvent::Paren(GroupEvent::End)));
                }
                let (event, range) = tokens.pop_front().unwrap();
                assert!(matches!(event,
                                 TokenEvent::Token(Token::Identifier(identifier, IdentifierType::Unquoted))
                                     if get_mapping_kind(&identifier) == Some(mapping_kind)));
                range.end
            }
        }
    }

    fn output_mapping_source(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        separator: Option<char>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        parameterizations: &[&Parameterization<'a>],
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<Src::Marker> {
        let get_mapping_kind = |identifier: &str| param_kind.mapping_kind(identifier);

        let mut end = None;

        loop {
            let (content_len, full_len, paren, mapping_kind) =
                self.analyze_data_segment(tokens, separator, get_mapping_kind);

            if let Some(mapping_kind) = mapping_kind {
                if matches!(mapping_kind.notation(), MappingNotation::Prefix) && content_len > 0 {
                    tokens.with_subslice(content_len, |param_tokens| {
                        end = self.output_mapping_param(
                            param_tokens,
                            out,
                            param_kind,
                            parameterizations,
                            result_params,
                        );
                        assert!(param_tokens.is_empty());
                    });
                    let end_ref = end.as_ref().unwrap();
                    self.source.diagnostic(
                        &end_ref..&end_ref,
                        Severity::Error,
                        format!("',' expected"),
                    );
                }

                let (_, range) = tokens.front().unwrap();
                out(
                    ParameterEvent::MappingParam(GroupEvent::Start(())),
                    &range.start..&range.start,
                );
                out(
                    ParameterEvent::Mapping(GroupEvent::Start(mapping_kind)),
                    &range.start..&range.start,
                );

                let mut source_params = Some(Vec::new());
                end = Some(self.output_mapping_source_by_notation(
                    tokens,
                    out,
                    mapping_kind,
                    paren,
                    content_len,
                    get_mapping_kind,
                    &mut source_params,
                ));

                let end = self.output_param(
                    tokens,
                    out,
                    param_kind,
                    &Parameterization::concat(parameterizations, source_params.as_deref()),
                    result_params,
                );

                let mapping_end = end.as_ref().unwrap();
                out(
                    ParameterEvent::Mapping(GroupEvent::End),
                    mapping_end..mapping_end,
                );
                out(
                    ParameterEvent::MappingParam(GroupEvent::End),
                    mapping_end..mapping_end,
                );

                if let Some((event, range)) = tokens.front() {
                    match event {
                        TokenEvent::Token(Token::ReservedChar(',', _, _)) => {
                            tokens.pop_front();
                        }
                        TokenEvent::Token(Token::ReservedChar(';', _, _)) => {
                            self.source.diagnostic(
                                &range.start..&range.end,
                                Severity::Error,
                                format!("expected comma instead of semicolon"),
                            );
                            tokens.pop_front();
                        }
                        _ => {
                            self.source.diagnostic(
                                &mapping_end..&mapping_end,
                                Severity::Error,
                                format!("',' expected"),
                            );
                        }
                    }
                } else {
                    break;
                }
            } else if full_len > 0 {
                if content_len > 0 {
                    tokens.with_subslice(content_len, |param_tokens| {
                        end = self.output_mapping_param(
                            param_tokens,
                            out,
                            param_kind,
                            parameterizations,
                            result_params,
                        );
                        assert!(param_tokens.is_empty());
                    });
                }

                if full_len > content_len {
                    assert_eq!(full_len, content_len + 1);
                    let (event, range) = tokens.pop_front().unwrap();
                    match event {
                        TokenEvent::Token(Token::ReservedChar(',', _, _)) => {
                            if content_len == 0 {
                                self.source.diagnostic(
                                    &range.start..&range.end,
                                    Severity::Error,
                                    format!("superfluous comma"),
                                );
                            }
                        }
                        TokenEvent::Token(Token::ReservedChar(';', _, _)) => {
                            self.source.diagnostic(
                                &range.start..&range.end,
                                Severity::Error,
                                format!("expected comma instead of semicolon"),
                            );
                        }
                        _ => panic!("unexpected end of segment"),
                    }
                }
            } else {
                break;
            }
        }

        end
    }

    fn output_mapping_param(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        parameterizations: &[&Parameterization<'a>],
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<Src::Marker> {
        let (_, range) = tokens.front().unwrap();
        let start = range.start.clone();
        out(
            ParameterEvent::MappingParam(GroupEvent::Start(())),
            &start..&start,
        );
        let end =
            self.output_single_param(tokens, out, param_kind, parameterizations, result_params);
        let end_ref = end.as_ref().unwrap();
        out(
            ParameterEvent::MappingParam(GroupEvent::End),
            end_ref..end_ref,
        );
        end
    }

    fn output_single_param(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        parameterizations: &[&Parameterization<'a>],
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<Src::Marker> {
        let end = self.output_param(tokens, out, param_kind, parameterizations, result_params);
        if let Some((_, range)) = tokens.pop_front() {
            self.source.diagnostic(
                &range.start..&range.end,
                Severity::Error,
                format!("unexpected delimiter"),
            );
            while tokens.pop_front().is_some() {}
        }
        end
    }

    fn output_param(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        parameterizations: &[&Parameterization<'a>],
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<Src::Marker> {
        let mut end = None;
        let mut state = ParamGroupState::new();

        loop {
            let mut event = None;
            let mut range_holder = None;
            let range: Range<&Src::Marker>;
            if let Some((cur_event, cur_range)) = tokens.pop_front() {
                event = Some(cur_event);
                range_holder = Some(cur_range);
                let range_holder_ref = range_holder.as_ref().unwrap();
                range = &range_holder_ref.start..&range_holder_ref.end;
            } else {
                let end_ref = end.as_ref().unwrap();
                range = end_ref..end_ref;
            }

            if let Some((event, _)) = self.param_group_event(
                &mut state,
                event,
                range,
                out,
                param_kind,
                None,
                parameterizations,
                None,
                result_params,
            ) {
                if let Some(event) = event {
                    tokens.push_front((event, range_holder.unwrap()));
                }
                break;
            } else if let Some(range_holder) = range_holder {
                end = Some(range_holder.end);
            }
        }

        end
    }

    fn output_object(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        object_kind: &'a dyn ObjectKind,
    ) {
        loop {
            let (event, range) = tokens.front().unwrap();
            if matches!(event, TokenEvent::Paren(GroupEvent::End)) {
                break;
            }
            let start = range.start.clone();
            out(
                ParameterEvent::ObjectItem(GroupEvent::Start(())),
                &start..&start,
            );
            let end = self
                .output_object_item(tokens, out, object_kind)
                .unwrap_or(start);
            out(ParameterEvent::ObjectItem(GroupEvent::End), &end..&end);
        }
    }

    fn output_object_item(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        object_kind: &'a dyn ObjectKind,
    ) -> Option<Src::Marker> {
        let separator = object_kind.separator();

        let mut param_tokens = self.extract_recorded_tokens(tokens, Some(separator));
        if self.skip_separator_and_check_end(tokens, separator) {
            return self.output_single_param(
                &mut RecordedTokenSlice::new(&mut param_tokens),
                out,
                object_kind.param_kind(),
                &[],
                &mut None,
            );
        }

        let mut parameterizations = Some(Vec::new());
        let end = self.output_object_item_parameterizations(
            tokens,
            out,
            object_kind.parameterization(),
            Some(separator),
            &mut parameterizations,
        );
        self.output_single_param(
            &mut RecordedTokenSlice::new(&mut param_tokens),
            out,
            object_kind.param_kind(),
            &Parameterization::concat(&[], parameterizations.as_deref()),
            &mut None,
        );
        if self.skip_separator_and_check_end(tokens, separator) {
            return end;
        }

        let mut extra_data_idx = 0;
        loop {
            let end = self.output_object_item_extra(
                tokens,
                out,
                object_kind.extra_data_kind(extra_data_idx),
                Some(separator),
            );
            if self.skip_separator_and_check_end(tokens, separator) {
                return end;
            }
            extra_data_idx += 1;
        }
    }

    fn skip_separator_and_check_end(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        separator: char,
    ) -> bool {
        if matches!(
            tokens.front().unwrap(),
            (TokenEvent::Paren(GroupEvent::End), _)
        ) {
            return true;
        }
        tokens.pop_front();

        if matches!(
            tokens.front().unwrap(),
            (TokenEvent::Token(Token::ReservedChar(c, _, _)), _) if *c == separator
        ) {
            tokens.pop_front();

            while matches!(
                tokens.front().unwrap(),
                (TokenEvent::Token(Token::ReservedChar(c, _, _)), _) if *c == separator
            ) {
                let (_, range) = tokens.pop_front().unwrap();
                self.source.diagnostic(
                    &range.start..&range.end,
                    Severity::Error,
                    format!("superfluous separator"),
                );
            }

            return true;
        }

        false
    }

    fn extract_recorded_tokens(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        separator: Option<char>,
    ) -> RecordedTokens<'a, Src::Marker> {
        let mut paren_depth: u32 = 0;
        let mut end_idx = 0;

        for (idx, (event, _)) in tokens.iter().enumerate() {
            match event {
                TokenEvent::Token(Token::ReservedChar(c, _, _))
                    if paren_depth == 0 && Some(*c) == separator =>
                {
                    break;
                }
                TokenEvent::Paren(GroupEvent::Start(_)) => {
                    paren_depth += 1;
                }
                TokenEvent::Paren(GroupEvent::End) => {
                    if paren_depth > 0 {
                        paren_depth -= 1;
                    } else {
                        break;
                    }
                }
                _ => {}
            }

            end_idx = idx + 1;
        }

        tokens.with_subslice(end_idx, |result| result.into_queue())
    }

    fn output_object_item_parameterizations(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        parameterization_kind: &'a dyn SectionKind,
        separator: Option<char>,
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<Src::Marker> {
        let (_, range) = tokens.front().unwrap();
        out(
            ParameterEvent::Parameterization(GroupEvent::Start(parameterization_kind)),
            &range.start..&range.start,
        );

        let mut end = range.start.clone();
        let mut state = SectionState::Start;

        loop {
            let (event, range) = tokens.pop_front().unwrap();
            if let Some((event, _)) = self.section_event(
                &mut state,
                Some(event),
                &range.start..&range.end,
                out,
                parameterization_kind,
                separator,
                &[],
                result_params,
            ) {
                tokens.push_front((event.unwrap(), range));
                break;
            } else {
                end = range.end;
            }
        }

        out(
            ParameterEvent::Parameterization(GroupEvent::End),
            &end..&end,
        );

        Some(end)
    }

    fn output_object_item_extra(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        data_kind: Option<&'a dyn DataKind>,
        separator: Option<char>,
    ) -> Option<Src::Marker> {
        let (_, range) = tokens.front().unwrap();
        let start = range.start.clone();
        out(
            ParameterEvent::ObjectItemExtra(GroupEvent::Start(())),
            &start..&start,
        );

        let end = self.output_data(tokens, separator, out, data_kind);

        let end_or_start = end.as_ref().unwrap_or(&start);
        out(
            ParameterEvent::ObjectItemExtra(GroupEvent::End),
            end_or_start..end_or_start,
        );

        end
    }
}

#[derive(Clone, PartialEq)]
pub enum ParameterIdentifierState<'a, Marker: Clone + PartialEq> {
    Start,
    AfterKeyword,
    AfterName {
        name: Cow<'a, str>,
        name_range: Range<Marker>,
    },
    MetaModelSucceeded {
        metamodel: &'a dyn MetaModel,
        section_state: SectionState<'a, Marker>,
    },
    MetaModelFailed,
}

pub type RecordedTokens<'a, Marker> = VecDeque<(TokenEvent<'a>, Range<Marker>)>;

type RecordedTokenSlice<'a, 'b, Marker> = QueueSlice<'b, (TokenEvent<'a>, Range<Marker>)>;

#[derive(Clone, PartialEq)]
pub enum SectionState<'a, Marker: Clone + PartialEq> {
    Start,
    Item {
        parameterizations: Option<Vec<Parameterization<'a>>>,
        item_state: SectionItemState<'a, Marker>,
    },
}

#[derive(Clone, PartialEq)]
pub enum SectionItemState<'a, Marker: Clone + PartialEq> {
    Start,
    Parameterization(&'a dyn SectionKind, Box<SectionState<'a, Marker>>),
    ParamGroup {
        group_state: ParamGroupState<'a, Marker>,
        end_marker: Marker,
    },
    Subsection(&'a dyn SectionKind, Box<SectionState<'a, Marker>>),
    AfterSubsection,
}

#[derive(Clone, PartialEq)]
pub struct ParamGroupState<'a, Marker: Clone + PartialEq> {
    recorded_tokens: RecordedTokens<'a, Marker>,
    paren_depth: u32,
    notation_len: usize,
    in_data: bool,
}

impl<'a, Marker: Clone + PartialEq> ParamGroupState<'a, Marker> {
    fn new() -> Self {
        ParamGroupState {
            recorded_tokens: VecDeque::new(),
            paren_depth: 0,
            notation_len: 0,
            in_data: false,
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct Parameterization<'a> {
    notation: NotationExpression<'a>,
}

impl<'a> Parameterization<'a> {
    fn concat<'b, 'c>(outer: &'c [&'b Self], inner: Option<&'b [Self]>) -> Cow<'c, [&'b Self]> {
        if let Some(inner) = inner {
            let mut result = Vec::with_capacity(outer.len() + inner.len());
            result.extend(outer);
            result.extend(inner);
            Cow::Owned(result)
        } else {
            Cow::Borrowed(outer)
        }
    }
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
        let metamodel = TestMetaModel;
        test_parameter_identification("%slate \"test\";", &metamodel, Vec::new(), &[])?;
        test_parameter_identification(
            "%slate \"test\"; x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    Vec::new(),
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x : T;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x : T := y;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("y".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x. T;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    vec![
                        DataToken::Token(Token::ReservedChar(
                            '.',
                            TokenIsolation::StronglyConnected,
                            TokenIsolation::Isolated,
                        )),
                        DataToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x ⎿T⏌ := y;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    vec![
                        DataToken::Paren(
                            '⎿',
                            vec![DataToken::Token(Token::Identifier(
                                "T".into(),
                                IdentifierType::Unquoted,
                            ))],
                        ),
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("y".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; (x) : T := y;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Paren(
                            '(',
                            vec![NotationExpression::Identifier("x".into())],
                        ),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("y".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x ↦ y;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier("↦".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("y".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; (x : T) := y;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    Vec::new(),
                    vec![
                        DataToken::Paren(
                            '(',
                            vec![
                                DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::Identifier(
                                    "T".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("y".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x : T; y : U;",
            &metamodel,
            vec![
                SectionItem {
                    parameterizations: Vec::new(),
                    body: SectionItemBody::ParamGroup(
                        vec![Parameter {
                            notation: NotationExpression::Identifier("x".into()),
                        }],
                        vec![
                            DataToken::Token(Token::Identifier(
                                ":".into(),
                                IdentifierType::Unquoted,
                            )),
                            DataToken::Token(Token::Identifier(
                                "T".into(),
                                IdentifierType::Unquoted,
                            )),
                        ],
                    ),
                },
                SectionItem {
                    parameterizations: Vec::new(),
                    body: SectionItemBody::ParamGroup(
                        vec![Parameter {
                            notation: NotationExpression::Identifier("y".into()),
                        }],
                        vec![
                            DataToken::Token(Token::Identifier(
                                ":".into(),
                                IdentifierType::Unquoted,
                            )),
                            DataToken::Token(Token::Identifier(
                                "U".into(),
                                IdentifierType::Unquoted,
                            )),
                        ],
                    ),
                },
            ],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x y;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Identifier("y".into()),
                        ]),
                    }],
                    Vec::new(),
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x^y_z;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::ReservedChar('^'),
                            NotationExpression::Identifier("y".into()),
                            NotationExpression::ReservedChar('_'),
                            NotationExpression::Identifier("z".into()),
                        ]),
                    }],
                    Vec::new(),
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x y %z(a;b);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Identifier("y".into()),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Keyword("%z".into())),
                        DataToken::Paren(
                            '(',
                            vec![
                                DataToken::Token(Token::Identifier(
                                    "a".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::ReservedChar(
                                    ';',
                                    TokenIsolation::StronglyConnected,
                                    TokenIsolation::StronglyConnected,
                                )),
                                DataToken::Token(Token::Identifier(
                                    "b".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x();",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren('(', Vec::new()),
                        ]),
                    }],
                    Vec::new(),
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(,);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren('(', Vec::new()),
                        ]),
                    }],
                    Vec::new(),
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y,z);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
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
                    Vec::new(),
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y,z,);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
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
                    Vec::new(),
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(,y,z,);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
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
                    Vec::new(),
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y,,z,);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
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
                    Vec::new(),
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y,z,,);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
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
                    Vec::new(),
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(y;z);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("y".into()),
                                    NotationExpression::Identifier("z".into()),
                                ])],
                            ),
                        ]),
                    }],
                    Vec::new(),
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ";".into(),
                severity: Severity::Error,
                msg: "token not allowed in notation".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(42);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("x".into()),
                            NotationExpression::Paren('(', Vec::new()),
                        ]),
                    }],
                    Vec::new(),
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "42".into(),
                severity: Severity::Error,
                msg: "token not allowed in notation".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x,y;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![
                        Parameter {
                            notation: NotationExpression::Identifier("x".into()),
                        },
                        Parameter {
                            notation: NotationExpression::Identifier("y".into()),
                        },
                    ],
                    Vec::new(),
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x,y : T;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![
                        Parameter {
                            notation: NotationExpression::Identifier("x".into()),
                        },
                        Parameter {
                            notation: NotationExpression::Identifier("y".into()),
                        },
                    ],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x,,y : T;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![
                        Parameter {
                            notation: NotationExpression::Identifier("x".into()),
                        },
                        Parameter {
                            notation: NotationExpression::Identifier("y".into()),
                        },
                    ],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; 42;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(Vec::new(), Vec::new()),
            }],
            &[TestDiagnosticMessage {
                range_text: "42".into(),
                severity: Severity::Error,
                msg: "token not allowed in notation".into(),
            }],
        )?;
        Ok(())
    }

    #[test]
    fn parameterizations() -> Result<(), Message> {
        let metamodel = TestMetaModel;
        test_parameter_identification(
            "%slate \"test\"; [b : B] a : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: Vec::new(),
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Identifier("b".into()),
                            }],
                            vec![
                                DataToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::Identifier(
                                    "B".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    }],
                )],
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("a".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [b : B] a(b) : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: Vec::new(),
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Identifier("b".into()),
                            }],
                            vec![
                                DataToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::Identifier(
                                    "B".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    }],
                )],
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("a".into()),
                            NotationExpression::Paren('(', vec![NotationExpression::Param(0)]),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[d : D] b,c : B] a : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: vec![Parameterization(
                            &metamodel,
                            vec![SectionItem {
                                parameterizations: Vec::new(),
                                body: SectionItemBody::ParamGroup(
                                    vec![Parameter {
                                        notation: NotationExpression::Identifier("d".into()),
                                    }],
                                    vec![
                                        DataToken::Token(Token::Identifier(
                                            ":".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        DataToken::Token(Token::Identifier(
                                            "D".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                ),
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![
                                Parameter {
                                    notation: NotationExpression::Identifier("b".into()),
                                },
                                Parameter {
                                    notation: NotationExpression::Identifier("c".into()),
                                },
                            ],
                            vec![
                                DataToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::Identifier(
                                    "B".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    }],
                )],
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("a".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[d : D] b; c : C] a : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![
                        SectionItem {
                            parameterizations: vec![Parameterization(
                                &metamodel,
                                vec![SectionItem {
                                    parameterizations: Vec::new(),
                                    body: SectionItemBody::ParamGroup(
                                        vec![Parameter {
                                            notation: NotationExpression::Identifier("d".into()),
                                        }],
                                        vec![
                                            DataToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            DataToken::Token(Token::Identifier(
                                                "D".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    ),
                                }],
                            )],
                            body: SectionItemBody::ParamGroup(
                                vec![Parameter {
                                    notation: NotationExpression::Identifier("b".into()),
                                }],
                                Vec::new(),
                            ),
                        },
                        SectionItem {
                            parameterizations: Vec::new(),
                            body: SectionItemBody::ParamGroup(
                                vec![Parameter {
                                    notation: NotationExpression::Identifier("c".into()),
                                }],
                                vec![
                                    DataToken::Token(Token::Identifier(
                                        ":".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                    DataToken::Token(Token::Identifier(
                                        "C".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                ],
                            ),
                        },
                    ],
                )],
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("a".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[d : D] b : B, c : C] a : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![
                        SectionItem {
                            parameterizations: vec![Parameterization(
                                &metamodel,
                                vec![SectionItem {
                                    parameterizations: Vec::new(),
                                    body: SectionItemBody::ParamGroup(
                                        vec![Parameter {
                                            notation: NotationExpression::Identifier("d".into()),
                                        }],
                                        vec![
                                            DataToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            DataToken::Token(Token::Identifier(
                                                "D".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    ),
                                }],
                            )],
                            body: SectionItemBody::ParamGroup(
                                vec![Parameter {
                                    notation: NotationExpression::Identifier("b".into()),
                                }],
                                vec![
                                    DataToken::Token(Token::Identifier(
                                        ":".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                    DataToken::Token(Token::Identifier(
                                        "B".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                ],
                            ),
                        },
                        SectionItem {
                            parameterizations: Vec::new(),
                            body: SectionItemBody::ParamGroup(
                                vec![Parameter {
                                    notation: NotationExpression::Identifier("c".into()),
                                }],
                                vec![
                                    DataToken::Token(Token::Identifier(
                                        ":".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                    DataToken::Token(Token::Identifier(
                                        "C".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                ],
                            ),
                        },
                    ],
                )],
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("a".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "expected semicolon instead of comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[d : D] b(d),c(d) : B] a(d ↦ b(d), d ↦ c(d)) : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: vec![Parameterization(
                            &metamodel,
                            vec![SectionItem {
                                parameterizations: Vec::new(),
                                body: SectionItemBody::ParamGroup(
                                    vec![Parameter {
                                        notation: NotationExpression::Identifier("d".into()),
                                    }],
                                    vec![
                                        DataToken::Token(Token::Identifier(
                                            ":".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        DataToken::Token(Token::Identifier(
                                            "D".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                ),
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![
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
                            vec![
                                DataToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::Identifier(
                                    "B".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    }],
                )],
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("a".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(0), NotationExpression::Param(1)],
                            ),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[[e : E] d(e) : D] b(e ↦ d(e)),c(e ↦ d(e)) : B] a(([e] d(e)) ↦ b(e ↦ d(e)), ([e] d(e)) ↦ c(e ↦ d(e))) : A;",&metamodel, 
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                    parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                            parameterizations: Vec::new(),
                            body: SectionItemBody::ParamGroup(
                                vec![Parameter {
                                    notation: NotationExpression::Identifier("e".into()),
                                }],
                                vec![
                                    DataToken::Token(Token::Identifier(
                                        ":".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                    DataToken::Token(Token::Identifier(
                                        "E".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                ],
                            ),
                        }])],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("d".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0)],
                                    ),
                                ]),
                            }],
                            vec![
                                DataToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::Identifier(
                                    "D".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    }])],
                    body: SectionItemBody::ParamGroup(
                        vec![
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
                        vec![
                            DataToken::Token(Token::Identifier(
                                ":".into(),
                                IdentifierType::Unquoted,
                            )),
                            DataToken::Token(Token::Identifier(
                                "B".into(),
                                IdentifierType::Unquoted,
                            )),
                        ],
                    ),
                }])],
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Identifier("a".into()),
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(0), NotationExpression::Param(1)],
                            ),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn sections() -> Result<(), Message> {
        let metamodel = TestMetaModel;
        test_parameter_identification(
            "%slate \"test\"; {}",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::Section(&metamodel, Vec::new()),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; {};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::Section(&metamodel, Vec::new()),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; { x : T }",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::Section(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: Vec::new(),
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Identifier("x".into()),
                            }],
                            vec![
                                DataToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::Identifier(
                                    "T".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    }],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; { x : T; }",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::Section(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: Vec::new(),
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Identifier("x".into()),
                            }],
                            vec![
                                DataToken::Token(Token::Identifier(
                                    ":".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::Identifier(
                                    "T".into(),
                                    IdentifierType::Unquoted,
                                )),
                            ],
                        ),
                    }],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; { x : T; y : U; }",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::Section(
                    &metamodel,
                    vec![
                        SectionItem {
                            parameterizations: Vec::new(),
                            body: SectionItemBody::ParamGroup(
                                vec![Parameter {
                                    notation: NotationExpression::Identifier("x".into()),
                                }],
                                vec![
                                    DataToken::Token(Token::Identifier(
                                        ":".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                    DataToken::Token(Token::Identifier(
                                        "T".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                ],
                            ),
                        },
                        SectionItem {
                            parameterizations: Vec::new(),
                            body: SectionItemBody::ParamGroup(
                                vec![Parameter {
                                    notation: NotationExpression::Identifier("y".into()),
                                }],
                                vec![
                                    DataToken::Token(Token::Identifier(
                                        ":".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                    DataToken::Token(Token::Identifier(
                                        "U".into(),
                                        IdentifierType::Unquoted,
                                    )),
                                ],
                            ),
                        },
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [a,b] { x_a; [c] y_(a,b,c); } z_a",
            &metamodel,
            vec![
                SectionItem {
                    parameterizations: vec![Parameterization(
                        &metamodel,
                        vec![SectionItem {
                            parameterizations: Vec::new(),
                            body: SectionItemBody::ParamGroup(
                                vec![
                                    Parameter {
                                        notation: NotationExpression::Identifier("a".into()),
                                    },
                                    Parameter {
                                        notation: NotationExpression::Identifier("b".into()),
                                    },
                                ],
                                Vec::new(),
                            ),
                        }],
                    )],
                    body: SectionItemBody::Section(
                        &metamodel,
                        vec![
                            SectionItem {
                                parameterizations: Vec::new(),
                                body: SectionItemBody::ParamGroup(
                                    vec![Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("x".into()),
                                            NotationExpression::ReservedChar('_'),
                                            NotationExpression::Param(0),
                                        ]),
                                    }],
                                    Vec::new(),
                                ),
                            },
                            SectionItem {
                                parameterizations: vec![Parameterization(
                                    &metamodel,
                                    vec![SectionItem {
                                        parameterizations: Vec::new(),
                                        body: SectionItemBody::ParamGroup(
                                            vec![Parameter {
                                                notation: NotationExpression::Identifier(
                                                    "c".into(),
                                                ),
                                            }],
                                            Vec::new(),
                                        ),
                                    }],
                                )],
                                body: SectionItemBody::ParamGroup(
                                    vec![Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("y".into()),
                                            NotationExpression::ReservedChar('_'),
                                            NotationExpression::Paren(
                                                '(',
                                                vec![
                                                    NotationExpression::Param(0),
                                                    NotationExpression::Param(1),
                                                    NotationExpression::Param(2),
                                                ],
                                            ),
                                        ]),
                                    }],
                                    Vec::new(),
                                ),
                            },
                        ],
                    ),
                },
                SectionItem {
                    parameterizations: Vec::new(),
                    body: SectionItemBody::ParamGroup(
                        vec![Parameter {
                            notation: NotationExpression::Sequence(vec![
                                NotationExpression::Identifier("z".into()),
                                NotationExpression::ReservedChar('_'),
                                NotationExpression::Identifier("a".into()),
                            ]),
                        }],
                        Vec::new(),
                    ),
                },
            ],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn objects() -> Result<(), Message> {
        let metamodel = TestMetaModel;
        test_parameter_identification(
            "%slate \"test\"; T := {};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Object(&metamodel, Vec::new()),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {x};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Object(
                            &metamodel,
                            vec![ObjectItem {
                                parameterizations: Vec::new(),
                                param: Parameter {
                                    notation: NotationExpression::Identifier("x".into()),
                                },
                                param_data: Vec::new(),
                                additional_data: Vec::new(),
                            }],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {x || y};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Object(
                            &metamodel,
                            vec![
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("x".into()),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("y".into()),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                            ],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {x | | y};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Object(
                            &metamodel,
                            vec![
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("x".into()),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("y".into()),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                            ],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {x ||| y};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Object(
                            &metamodel,
                            vec![
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("x".into()),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("y".into()),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                            ],
                        ),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "|".into(),
                severity: Severity::Error,
                msg: "superfluous separator".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {x(y) | y | z};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Object(
                            &metamodel,
                            vec![ObjectItem {
                                parameterizations: vec![Parameterization(
                                    &metamodel,
                                    vec![SectionItem {
                                        parameterizations: Vec::new(),
                                        body: SectionItemBody::ParamGroup(
                                            vec![Parameter {
                                                notation: NotationExpression::Identifier(
                                                    "y".into(),
                                                ),
                                            }],
                                            Vec::new(),
                                        ),
                                    }],
                                )],
                                param: Parameter {
                                    notation: NotationExpression::Sequence(vec![
                                        NotationExpression::Identifier("x".into()),
                                        NotationExpression::Paren(
                                            '(',
                                            vec![NotationExpression::Param(0)],
                                        ),
                                    ]),
                                },
                                param_data: Vec::new(),
                                additional_data: vec![vec![DataToken::Token(Token::Identifier(
                                    "z".into(),
                                    IdentifierType::Unquoted,
                                ))]],
                            }],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {x(y) | y || z};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Object(
                            &metamodel,
                            vec![
                                ObjectItem {
                                    parameterizations: vec![Parameterization(
                                        &metamodel,
                                        vec![SectionItem {
                                            parameterizations: Vec::new(),
                                            body: SectionItemBody::ParamGroup(
                                                vec![Parameter {
                                                    notation: NotationExpression::Identifier(
                                                        "y".into(),
                                                    ),
                                                }],
                                                Vec::new(),
                                            ),
                                        }],
                                    )],
                                    param: Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("x".into()),
                                            NotationExpression::Paren(
                                                '(',
                                                vec![NotationExpression::Param(0)],
                                            ),
                                        ]),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("z".into()),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                            ],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {x_i ↦ i | i : I || y_j ↦ j | j : J | a | b} | {z};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("T".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Object(
                            &metamodel,
                            vec![
                                ObjectItem {
                                    parameterizations: vec![Parameterization(
                                        &metamodel,
                                        vec![SectionItem {
                                            parameterizations: Vec::new(),
                                            body: SectionItemBody::ParamGroup(
                                                vec![Parameter {
                                                    notation: NotationExpression::Identifier(
                                                        "i".into(),
                                                    ),
                                                }],
                                                vec![
                                                    DataToken::Token(Token::Identifier(
                                                        ":".into(),
                                                        IdentifierType::Unquoted,
                                                    )),
                                                    DataToken::Token(Token::Identifier(
                                                        "I".into(),
                                                        IdentifierType::Unquoted,
                                                    )),
                                                ],
                                            ),
                                        }],
                                    )],
                                    param: Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("x".into()),
                                            NotationExpression::ReservedChar('_'),
                                            NotationExpression::Param(0),
                                        ]),
                                    },
                                    param_data: vec![
                                        DataToken::Token(Token::Identifier(
                                            "↦".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        DataToken::Token(Token::Identifier(
                                            "i".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                    additional_data: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: vec![Parameterization(
                                        &metamodel,
                                        vec![SectionItem {
                                            parameterizations: Vec::new(),
                                            body: SectionItemBody::ParamGroup(
                                                vec![Parameter {
                                                    notation: NotationExpression::Identifier(
                                                        "j".into(),
                                                    ),
                                                }],
                                                vec![
                                                    DataToken::Token(Token::Identifier(
                                                        ":".into(),
                                                        IdentifierType::Unquoted,
                                                    )),
                                                    DataToken::Token(Token::Identifier(
                                                        "J".into(),
                                                        IdentifierType::Unquoted,
                                                    )),
                                                ],
                                            ),
                                        }],
                                    )],
                                    param: Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("y".into()),
                                            NotationExpression::ReservedChar('_'),
                                            NotationExpression::Param(0),
                                        ]),
                                    },
                                    param_data: vec![
                                        DataToken::Token(Token::Identifier(
                                            "↦".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        DataToken::Token(Token::Identifier(
                                            "j".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                    additional_data: vec![
                                        vec![DataToken::Token(Token::Identifier(
                                            "a".into(),
                                            IdentifierType::Unquoted,
                                        ))],
                                        vec![DataToken::Token(Token::Identifier(
                                            "b".into(),
                                            IdentifierType::Unquoted,
                                        ))],
                                    ],
                                },
                            ],
                        ),
                        DataToken::Token(Token::ReservedChar(
                            '|',
                            TokenIsolation::Isolated,
                            TokenIsolation::Isolated,
                        )),
                        DataToken::Object(
                            &metamodel,
                            vec![ObjectItem {
                                parameterizations: Vec::new(),
                                param: Parameter {
                                    notation: NotationExpression::Identifier("z".into()),
                                },
                                param_data: Vec::new(),
                                additional_data: Vec::new(),
                            }],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; ℕ := {@\"0\" || S(n) | n : ℕ};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("ℕ".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Object(
                            &metamodel,
                            vec![
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("0".into()),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: vec![Parameterization(
                                        &metamodel,
                                        vec![SectionItem {
                                            parameterizations: Vec::new(),
                                            body: SectionItemBody::ParamGroup(
                                                vec![Parameter {
                                                    notation: NotationExpression::Identifier(
                                                        "n".into(),
                                                    ),
                                                }],
                                                vec![
                                                    DataToken::Token(Token::Identifier(
                                                        ":".into(),
                                                        IdentifierType::Unquoted,
                                                    )),
                                                    DataToken::Token(Token::Identifier(
                                                        "ℕ".into(),
                                                        IdentifierType::Unquoted,
                                                    )),
                                                ],
                                            ),
                                        }],
                                    )],
                                    param: Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("S".into()),
                                            NotationExpression::Paren(
                                                '(',
                                                vec![NotationExpression::Param(0)],
                                            ),
                                        ]),
                                    },
                                    param_data: Vec::new(),
                                    additional_data: Vec::new(),
                                },
                            ],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn prefix_mappings() -> Result<(), Message> {
        todo!()
    }

    #[test]
    fn infix_mappings() -> Result<(), Message> {
        let metamodel = TestMetaModel;
        test_parameter_identification(
            "%slate \"test\"; f := (() ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                Vec::new(),
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := (a ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                vec![MappingParameter(
                                    None,
                                    Parameter {
                                        notation: NotationExpression::Identifier("a".into()),
                                    },
                                    Vec::new(),
                                )],
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := (a : A ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                vec![MappingParameter(
                                    None,
                                    Parameter {
                                        notation: NotationExpression::Identifier("a".into()),
                                    },
                                    vec![
                                        DataToken::Token(Token::Identifier(
                                            ":".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        DataToken::Token(Token::Identifier(
                                            "A".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                )],
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := ((a) ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                vec![MappingParameter(
                                    None,
                                    Parameter {
                                        notation: NotationExpression::Identifier("a".into()),
                                    },
                                    Vec::new(),
                                )],
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := ((a : A) ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                vec![MappingParameter(
                                    None,
                                    Parameter {
                                        notation: NotationExpression::Identifier("a".into()),
                                    },
                                    vec![
                                        DataToken::Token(Token::Identifier(
                                            ":".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        DataToken::Token(Token::Identifier(
                                            "A".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                )],
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := (a, b ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![
                                DataToken::Token(Token::Identifier(
                                    "a".into(),
                                    IdentifierType::Unquoted,
                                )),
                                DataToken::Token(Token::ReservedChar(
                                    ',',
                                    TokenIsolation::StronglyConnected,
                                    TokenIsolation::Isolated,
                                )),
                                DataToken::Mapping(
                                    &metamodel,
                                    vec![MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("b".into()),
                                        },
                                        Vec::new(),
                                    )],
                                    vec![DataToken::Token(Token::Identifier(
                                        "x".into(),
                                        IdentifierType::Unquoted,
                                    ))],
                                ),
                            ],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := (a ↦ x, b ↦ y);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![
                                DataToken::Mapping(
                                    &metamodel,
                                    vec![MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("a".into()),
                                        },
                                        Vec::new(),
                                    )],
                                    vec![DataToken::Token(Token::Identifier(
                                        "x".into(),
                                        IdentifierType::Unquoted,
                                    ))],
                                ),
                                DataToken::Token(Token::ReservedChar(
                                    ',',
                                    TokenIsolation::StronglyConnected,
                                    TokenIsolation::Isolated,
                                )),
                                DataToken::Mapping(
                                    &metamodel,
                                    vec![MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("b".into()),
                                        },
                                        Vec::new(),
                                    )],
                                    vec![DataToken::Token(Token::Identifier(
                                        "y".into(),
                                        IdentifierType::Unquoted,
                                    ))],
                                ),
                            ],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := ((a,b) ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                vec![
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("a".into()),
                                        },
                                        Vec::new(),
                                    ),
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("b".into()),
                                        },
                                        Vec::new(),
                                    ),
                                ],
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := ((a,b,) ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                vec![
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("a".into()),
                                        },
                                        Vec::new(),
                                    ),
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("b".into()),
                                        },
                                        Vec::new(),
                                    ),
                                ],
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := ((a,,b) ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                vec![
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("a".into()),
                                        },
                                        Vec::new(),
                                    ),
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("b".into()),
                                        },
                                        Vec::new(),
                                    ),
                                ],
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := ((a : A, b : B) ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                vec![
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("a".into()),
                                        },
                                        vec![
                                            DataToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            DataToken::Token(Token::Identifier(
                                                "A".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    ),
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("b".into()),
                                        },
                                        vec![
                                            DataToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            DataToken::Token(Token::Identifier(
                                                "B".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    ),
                                ],
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := ((a : A, b : B ↦ c_b : C) ↦ x);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '(',
                            vec![DataToken::Mapping(
                                &metamodel,
                                vec![
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("a".into()),
                                        },
                                        vec![
                                            DataToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            DataToken::Token(Token::Identifier(
                                                "A".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    ),
                                    MappingParameter(
                                        Some(MappingParameterization(
                                            &metamodel,
                                            vec![MappingParameter(
                                                None,
                                                Parameter {
                                                    notation: NotationExpression::Identifier(
                                                        "b".into(),
                                                    ),
                                                },
                                                vec![
                                                    DataToken::Token(Token::Identifier(
                                                        ":".into(),
                                                        IdentifierType::Unquoted,
                                                    )),
                                                    DataToken::Token(Token::Identifier(
                                                        "B".into(),
                                                        IdentifierType::Unquoted,
                                                    )),
                                                ],
                                            )],
                                        )),
                                        Parameter {
                                            notation: NotationExpression::Sequence(vec![
                                                NotationExpression::Identifier("c".into()),
                                                NotationExpression::ReservedChar('_'),
                                                NotationExpression::Param(0),
                                            ]),
                                        },
                                        vec![
                                            DataToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            DataToken::Token(Token::Identifier(
                                                "C".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    ),
                                ],
                                vec![DataToken::Token(Token::Identifier(
                                    "x".into(),
                                    IdentifierType::Unquoted,
                                ))],
                            )],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        test_parameter_identification(
            "%slate \"test\"; a := f[(b : B) ↦ b, ((d : D, e : E, f : E) ↦ c[d,f] : C) ↦ c[0,1]];",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("a".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("f".into(), IdentifierType::Unquoted)),
                        DataToken::Paren(
                            '[',
                            vec![
                                DataToken::Mapping(
                                    &metamodel,
                                    vec![MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("b".into()),
                                        },
                                        vec![
                                            DataToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            DataToken::Token(Token::Identifier(
                                                "B".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    )],
                                    vec![DataToken::Token(Token::Identifier(
                                        "b".into(),
                                        IdentifierType::Unquoted,
                                    ))],
                                ),
                                DataToken::Token(Token::ReservedChar(
                                    ',',
                                    TokenIsolation::StronglyConnected,
                                    TokenIsolation::Isolated,
                                )),
                                DataToken::Mapping(
                                    &metamodel,
                                    vec![MappingParameter(
                                        Some(MappingParameterization(
                                            &metamodel,
                                            vec![
                                                MappingParameter(
                                                    None,
                                                    Parameter {
                                                        notation: NotationExpression::Identifier(
                                                            "d".into(),
                                                        ),
                                                    },
                                                    vec![
                                                        DataToken::Token(Token::Identifier(
                                                            ":".into(),
                                                            IdentifierType::Unquoted,
                                                        )),
                                                        DataToken::Token(Token::Identifier(
                                                            "D".into(),
                                                            IdentifierType::Unquoted,
                                                        )),
                                                    ],
                                                ),
                                                MappingParameter(
                                                    None,
                                                    Parameter {
                                                        notation: NotationExpression::Identifier(
                                                            "e".into(),
                                                        ),
                                                    },
                                                    vec![
                                                        DataToken::Token(Token::Identifier(
                                                            ":".into(),
                                                            IdentifierType::Unquoted,
                                                        )),
                                                        DataToken::Token(Token::Identifier(
                                                            "E".into(),
                                                            IdentifierType::Unquoted,
                                                        )),
                                                    ],
                                                ),
                                                MappingParameter(
                                                    None,
                                                    Parameter {
                                                        notation: NotationExpression::Identifier(
                                                            "f".into(),
                                                        ),
                                                    },
                                                    vec![
                                                        DataToken::Token(Token::Identifier(
                                                            ":".into(),
                                                            IdentifierType::Unquoted,
                                                        )),
                                                        DataToken::Token(Token::Identifier(
                                                            "E".into(),
                                                            IdentifierType::Unquoted,
                                                        )),
                                                    ],
                                                ),
                                            ],
                                        )),
                                        Parameter {
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
                                        },
                                        vec![
                                            DataToken::Token(Token::Identifier(
                                                ":".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            DataToken::Token(Token::Identifier(
                                                "C".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                        ],
                                    )],
                                    vec![
                                        DataToken::Token(Token::Identifier(
                                            "c".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                        DataToken::Paren(
                                            '[',
                                            vec![
                                                DataToken::Token(Token::Number("0".into())),
                                                DataToken::Token(Token::ReservedChar(
                                                    ',',
                                                    TokenIsolation::StronglyConnected,
                                                    TokenIsolation::StronglyConnected,
                                                )),
                                                DataToken::Token(Token::Number("1".into())),
                                            ],
                                        ),
                                    ],
                                ),
                            ],
                        ),
                    ],
                ),
            }],
            &[],
        )?;
        Ok(())
    }

    #[test]
    fn top_level_errors() -> Result<(), Message> {
        let metamodel = TestMetaModel;
        test_parameter_identification_with_document(
            "",
            &metamodel,
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
        test_parameter_identification_with_document(
            "%slate \"unknown\";",
            &metamodel,
            Document {
                metamodel: None,
                definitions: Vec::new(),
            },
            &[TestDiagnosticMessage {
                range_text: "\"unknown\"".into(),
                severity: Severity::Error,
                msg: "unknown metamodel \"unknown\"".into(),
            }],
        )?;
        test_parameter_identification_with_document(
            "%slate \"test\" x",
            &metamodel,
            Document {
                metamodel: None,
                definitions: Vec::new(),
            },
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "';' expected".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\";; x",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    Vec::new(),
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ";".into(),
                severity: Severity::Warning,
                msg: "superfluous semicolon".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x : T;;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("T".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ";".into(),
                severity: Severity::Warning,
                msg: "superfluous semicolon".into(),
            }],
        )?;
        test_parameter_identification(
            "%slate \"test\"; {};;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::Section(&metamodel, Vec::new()),
            }],
            &[TestDiagnosticMessage {
                range_text: ";".into(),
                severity: Severity::Warning,
                msg: "superfluous semicolon".into(),
            }],
        )?;
        Ok(())
    }

    struct Document<'a> {
        metamodel: Option<&'a dyn MetaModel>,
        definitions: Vec<SectionItem<'a>>,
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for Document<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            if let Some(metamodel) = self.metamodel {
                result.push(ParameterEvent::MetaModel(metamodel));
            }
            self.definitions.fill_events(result);
        }
    }

    struct SectionItem<'a> {
        parameterizations: Vec<Parameterization<'a>>,
        body: SectionItemBody<'a>,
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for SectionItem<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            Self::group(
                (),
                result,
                |event| ParameterEvent::SectionItem(event),
                |result| {
                    self.parameterizations.fill_events(result);
                    self.body.fill_events(result);
                },
            );
        }
    }

    struct Parameterization<'a>(&'a dyn SectionKind, Vec<SectionItem<'a>>);

    impl<'a> IntoEvents<ParameterEvent<'a>> for Parameterization<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            Self::group(
                self.0,
                result,
                |event| ParameterEvent::Parameterization(event),
                |result| self.1.fill_events(result),
            );
        }
    }

    enum SectionItemBody<'a> {
        ParamGroup(Vec<Parameter<'a>>, Data<'a>),
        Section(&'a dyn SectionKind, Vec<SectionItem<'a>>),
    }

    impl<'a> SectionItemBody<'a> {
        fn item_type(&self) -> SectionItemType<'a> {
            match self {
                SectionItemBody::ParamGroup(_, _) => SectionItemType::ParamGroup,
                SectionItemBody::Section(section_kind, _) => {
                    SectionItemType::Section(*section_kind)
                }
            }
        }
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for SectionItemBody<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            Self::group(
                self.item_type(),
                result,
                |event| ParameterEvent::SectionItemBody(event),
                |result| match self {
                    SectionItemBody::ParamGroup(params, data) => {
                        params.fill_events(result);
                        data.fill_events(result);
                    }
                    SectionItemBody::Section(_, items) => {
                        items.fill_events(result);
                    }
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

    enum DataToken<'a> {
        Token(Token<'a>),
        Paren(char, Data<'a>),
        Mapping(&'a dyn MappingKind, Vec<MappingParameter<'a>>, Data<'a>),
        Object(&'a dyn ObjectKind, Vec<ObjectItem<'a>>),
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for DataToken<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            match self {
                DataToken::Token(token) => {
                    result.push(ParameterEvent::Token(TokenEvent::Token(token)))
                }
                DataToken::Paren(paren, contents) => {
                    Self::group(
                        paren,
                        result,
                        |event| ParameterEvent::Token(TokenEvent::Paren(event)),
                        |result| contents.fill_events(result),
                    );
                }
                DataToken::Mapping(mapping_kind, params, data) => {
                    Self::group(
                        mapping_kind,
                        result,
                        |event| ParameterEvent::Mapping(event),
                        |result| {
                            params.fill_events(result);
                            data.fill_events(result);
                        },
                    );
                }
                DataToken::Object(object_kind, items) => {
                    Self::group(
                        object_kind,
                        result,
                        |event| ParameterEvent::Object(event),
                        |result| items.fill_events(result),
                    );
                }
            }
        }
    }

    type Data<'a> = Vec<DataToken<'a>>;

    struct MappingParameter<'a>(Option<MappingParameterization<'a>>, Parameter<'a>, Data<'a>);

    impl<'a> IntoEvents<ParameterEvent<'a>> for MappingParameter<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            Self::group(
                (),
                result,
                |event| ParameterEvent::MappingParam(event),
                |result| {
                    if let Some(parameterization) = self.0 {
                        Self::group(
                            parameterization.0,
                            result,
                            |event| ParameterEvent::Mapping(event),
                            |result| {
                                parameterization.1.fill_events(result);
                                self.1.fill_events(result);
                                self.2.fill_events(result);
                            },
                        );
                    } else {
                        self.1.fill_events(result);
                        self.2.fill_events(result);
                    }
                },
            );
        }
    }

    struct MappingParameterization<'a>(&'a dyn MappingKind, Vec<MappingParameter<'a>>);

    struct ObjectItem<'a> {
        parameterizations: Vec<Parameterization<'a>>,
        param: Parameter<'a>,
        param_data: Data<'a>,
        additional_data: Vec<Data<'a>>,
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for ObjectItem<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            Self::group(
                (),
                result,
                |event| ParameterEvent::ObjectItem(event),
                |result| {
                    self.parameterizations.fill_events(result);
                    self.param.fill_events(result);
                    self.param_data.fill_events(result);
                    for data in self.additional_data {
                        Self::group(
                            (),
                            result,
                            |event| ParameterEvent::ObjectItemExtra(event),
                            |result| data.fill_events(result),
                        );
                    }
                },
            )
        }
    }

    fn test_parameter_identification(
        input: &str,
        metamodel: &TestMetaModel,
        expected_definitions: Vec<SectionItem>,
        expected_diagnostics: &[TestDiagnosticMessage],
    ) -> Result<(), Message> {
        let expected_document = Document {
            metamodel: Some(metamodel),
            definitions: expected_definitions,
        };
        test_parameter_identification_with_document(
            input,
            metamodel,
            expected_document,
            expected_diagnostics,
        )
    }

    fn test_parameter_identification_with_document(
        input: &str,
        metamodel: &TestMetaModel,
        expected_document: Document,
        expected_diagnostics: &[TestDiagnosticMessage],
    ) -> Result<(), Message> {
        let mut param_events = Vec::new();
        let param_sink =
            TranslatorInst::new(ParameterIdentifier::new(metamodel), &mut param_events);
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
