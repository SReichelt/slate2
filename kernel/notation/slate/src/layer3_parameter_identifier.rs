use std::{borrow::Cow, collections::VecDeque, ops::Range};

use slate_kernel_notation_generic::{event::*, event_source::*, event_translator::*};
use slate_kernel_util::queue_slice::*;

use crate::{chars::*, layer1_tokenizer::*, layer2_parenthesis_matcher::*, metamodel::*};

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
    Mapping(GroupEvent<&'a dyn MappingKind<dyn DataKind>>),
    MappingParam(GroupEvent<Option<&'a dyn MappingKind<dyn ParamKind>>>),
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
    Param(u32, Option<NotationParameterization<'a>>),
}

impl<'a> NotationExpression<'a> {
    fn contains_param(&self) -> bool {
        match self {
            NotationExpression::Param(_, _) => true,
            NotationExpression::Sequence(items) => items.iter().any(Self::contains_param),
            NotationExpression::Paren(_, items) => items.iter().any(Self::contains_param),
            _ => false,
        }
    }

    fn find_in<'b>(
        &self,
        parameterizations: &[&'b Parameterization<'a>],
    ) -> Option<(u32, &'b Parameterization<'a>)> {
        let mut param_idx = 0;
        for param in parameterizations {
            if *self == param.notation {
                return Some((param_idx, *param));
            }
            param_idx += 1;
        }
        None
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct NotationParameterization<'a> {
    pub mapping_kind: &'a dyn MappingKind<dyn ParamKind>,
    pub source_params: Vec<Option<NotationParameterization<'a>>>,
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
                if let Some(TokenEvent::Token(Token::String('"', name))) = event {
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
                    ParamScopeClass::Global,
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
        scope_class: ParamScopeClass,
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
                        scope_class,
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
                    scope_class,
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
                            scope_class,
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
        scope_class: ParamScopeClass,
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
                    param_state: ParamState::new(),
                    end_marker: range.start.clone(),
                };
                self.section_item_event(
                    parameterizations,
                    state,
                    event,
                    range,
                    out,
                    section_kind,
                    scope_class,
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
                    ParamScopeClass::Local,
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
                param_state,
                end_marker,
            } => {
                let end = range.end;
                if let Some((event, range)) = self.param_event(
                    param_state,
                    event,
                    range,
                    out,
                    section_kind.param_kind(),
                    scope_class,
                    separator,
                    None,
                    outer_parameterizations,
                    parameterizations.as_deref(),
                    result_params,
                ) {
                    if matches!(
                        event,
                        Some(TokenEvent::Token(Token::ReservedChar(',', _, _)))
                    ) && matches!(
                        param_state,
                        ParamState::Data(DataState::TopLevel(PlainDataState::TopLevel {
                            has_contents: false
                        }))
                    ) {
                        *param_state = ParamState::new();
                        *end_marker = range.end.clone();
                        None
                    } else {
                        out(
                            ParameterEvent::SectionItemBody(GroupEvent::End),
                            end_marker..end_marker,
                        );
                        out(
                            ParameterEvent::SectionItem(GroupEvent::End),
                            end_marker..end_marker,
                        );
                        Some((event, range))
                    }
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
                    scope_class,
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

    fn param_event<'b>(
        &self,
        state: &mut ParamState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        scope_class: ParamScopeClass,
        separator: Option<char>,
        additional_separator: Option<char>,
        outer_parameterizations: &[&Parameterization<'a>],
        inner_parameterizations: Option<&[Parameterization<'a>]>,
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        match state {
            ParamState::Notation(notation_state) => {
                if let Some((event, range)) = self.param_notation_event(
                    notation_state,
                    event,
                    range,
                    out,
                    param_kind.notation_kind(),
                    scope_class,
                    separator,
                    outer_parameterizations,
                    inner_parameterizations,
                    result_params,
                ) {
                    let mut data_state = ParamDataState::new();
                    while let Some((event, range)) = notation_state.recorded_tokens.pop_front() {
                        let result = self.param_data_event(
                            &mut data_state,
                            Some(event),
                            &range.start..&range.end,
                            out,
                            param_kind.data_kind(),
                            None,
                            None,
                        );
                        assert!(result.is_none());
                    }
                    *state = ParamState::Data(data_state);
                    self.param_event(
                        state,
                        event,
                        range,
                        out,
                        param_kind,
                        scope_class,
                        separator,
                        additional_separator,
                        outer_parameterizations,
                        inner_parameterizations,
                        result_params,
                    )
                } else {
                    None
                }
            }

            ParamState::Data(data_state) => self.param_data_event(
                data_state,
                event,
                range,
                out,
                param_kind.data_kind(),
                separator,
                additional_separator,
            ),
        }
    }

    fn param_notation_event<'b>(
        &self,
        state: &mut ParamNotationState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        notation_kind: Option<&'a dyn NotationKind>,
        scope_class: ParamScopeClass,
        separator: Option<char>,
        outer_parameterizations: &[&Parameterization<'a>],
        inner_parameterizations: Option<&[Parameterization<'a>]>,
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        if let Some((event, range, data_mapping_kind)) = self.param_notation_analysis_event(
            &mut state.recorded_tokens,
            &mut state.notation_len,
            &mut state.mapping_state,
            event,
            range,
            notation_kind,
            separator,
        ) {
            if state.notation_len > 0 {
                RecordedTokenSlice::new(&mut state.recorded_tokens).with_subslice(
                    state.notation_len,
                    |notation_tokens| {
                        self.output_notation(
                            notation_tokens,
                            out,
                            notation_kind.unwrap(),
                            scope_class,
                            data_mapping_kind,
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
            }

            Some((event, range))
        } else {
            None
        }
    }

    fn param_notation_analysis_event<'b>(
        &self,
        recorded_tokens: &mut RecordedTokens<'a, Src::Marker>,
        notation_len: &mut usize,
        mapping_state: &mut ParamNotationMappingAnalysisState<'a>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        notation_kind: Option<&'a dyn NotationKind>,
        separator: Option<char>,
    ) -> Option<(
        Option<TokenEvent<'a>>,
        Range<&'b Src::Marker>,
        Option<&'a dyn MappingKind<dyn ParamKind>>,
    )> {
        let Some(notation_kind) = notation_kind else { return Some((event, range, None)); };
        let Some(event) = event else { return Some((event, range, None)); };

        match mapping_state {
            ParamNotationMappingAnalysisState::TopLevel { paren_depth } => {
                match &event {
                    TokenEvent::Token(Token::ReservedChar(c, _, _))
                        if *paren_depth == 0
                            && (*c == ',' || *c == ';' || *c == '.' || Some(*c) == separator) =>
                    {
                        if *c == ',' && *notation_len == 0 {
                            self.source.diagnostic(
                                range.clone(),
                                Severity::Error,
                                format!("superfluous comma"),
                            );
                        }
                        return Some((Some(event), range, None));
                    }
                    TokenEvent::Token(Token::Keyword(_))
                    | TokenEvent::Token(Token::Number(_))
                    | TokenEvent::Token(Token::String(_, _)) => {
                        return Some((Some(event), range, None));
                    }
                    TokenEvent::Token(Token::Identifier(identifier, IdentifierType::Unquoted)) => {
                        if notation_kind.identifier_is_notation_delimiter(&identifier) {
                            return Some((Some(event), range, None));
                        } else if *paren_depth == 0 {
                            if let Some(mapping_kind) = notation_kind.mapping_kind(&identifier) {
                                match mapping_kind.notation() {
                                    MappingNotation::Prefix => {
                                        *mapping_state =
                                            ParamNotationMappingAnalysisState::PrefixMapping(
                                                mapping_kind,
                                                ParamNotationMappingState::Source(Box::new(
                                                    ParamNotationMappingAnalysisState::new(),
                                                )),
                                            );
                                        recorded_tokens.push_back((
                                            event,
                                            range.start.clone()..range.end.clone(),
                                        ));
                                        *notation_len = recorded_tokens.len();
                                        return None;
                                    }
                                    MappingNotation::Infix { binder_paren: _ } => {
                                        return Some((Some(event), range, Some(mapping_kind)));
                                    }
                                }
                            }
                        }
                    }
                    TokenEvent::Paren(GroupEvent::Start(start_paren)) => {
                        if notation_kind.paren_is_notation_delimiter(*start_paren) {
                            return Some((Some(event), range, None));
                        } else {
                            *paren_depth += 1;
                        }
                    }
                    TokenEvent::Paren(GroupEvent::End) => {
                        if *paren_depth > 0 {
                            *paren_depth -= 1;
                        } else {
                            return Some((Some(event), range, None));
                        }
                    }
                    _ => {}
                }

                recorded_tokens.push_back((event, range.start.clone()..range.end.clone()));
                if *paren_depth == 0 {
                    *notation_len = recorded_tokens.len();
                }
                None
            }

            ParamNotationMappingAnalysisState::PrefixMapping(
                mapping_kind,
                prefix_mapping_state,
            ) => match prefix_mapping_state {
                ParamNotationMappingState::Source(source_state) => {
                    if let Some((event, range, _)) = self.param_notation_analysis_event(
                        recorded_tokens,
                        notation_len,
                        source_state,
                        Some(event),
                        range,
                        mapping_kind.param_kind().notation_kind(),
                        separator,
                    ) {
                        match event {
                            Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                                if c == ',' || c == ';' || c == '.' =>
                            {
                                if c == '.' {
                                    *prefix_mapping_state = ParamNotationMappingState::Target(
                                        Box::new(ParamNotationMappingAnalysisState::new()),
                                    );
                                } else {
                                    *source_state.as_mut() =
                                        ParamNotationMappingAnalysisState::new();
                                }
                                recorded_tokens.push_back((
                                    event.unwrap(),
                                    range.start.clone()..range.end.clone(),
                                ));
                                *notation_len = recorded_tokens.len();
                                None
                            }
                            _ => Some((event, range, None)),
                        }
                    } else {
                        None
                    }
                }
                ParamNotationMappingState::Target(target_state) => self
                    .param_notation_analysis_event(
                        recorded_tokens,
                        notation_len,
                        target_state,
                        Some(event),
                        range,
                        mapping_kind.target_kind().notation_kind(),
                        separator,
                    ),
            },
        }
    }

    fn output_notation(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        notation_kind: &'a dyn NotationKind,
        scope_class: ParamScopeClass,
        data_mapping_kind: Option<&'a dyn MappingKind<dyn ParamKind>>,
        parameterizations: &[&Parameterization<'a>],
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> bool {
        if let Some((notation, range)) = self.create_notation_expression(
            tokens,
            notation_kind,
            Some(scope_class),
            data_mapping_kind,
            parameterizations,
            &mut vec![false; parameterizations.len()],
            false,
        ) {
            if matches!(notation, NotationExpression::Param(_, None)) {
                self.source.diagnostic(
                    &range.start..&range.end,
                    Severity::Error,
                    format!("notation cannot consist entirely of a parameter"),
                );
            }

            if let Some(result_params) = result_params {
                result_params.push(Parameterization {
                    notation: notation.clone(),
                    source_notations: parameterizations
                        .iter()
                        .map(|param| param.notation.clone())
                        .collect(),
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
        notation_kind: &'a dyn NotationKind,
        scope_class: Option<ParamScopeClass>,
        data_mapping_kind: Option<&'a dyn MappingKind<dyn ParamKind>>,
        parameterizations: &[&Parameterization<'a>],
        referenced_parameterizations: &mut [bool],
        is_in_mapping_target: bool,
    ) -> Option<(NotationExpression<'a>, Range<Src::Marker>)> {
        self.handle_notation_with_mapping_support(
            tokens,
            notation_kind,
            scope_class,
            data_mapping_kind,
            |tokens, mapping| {
                if let Some((mapping_kind, params, mapping_start)) = mapping {
                    self.create_mapping_target_expression(
                        tokens,
                        mapping_kind,
                        parameterizations,
                        referenced_parameterizations,
                        params,
                        mapping_start,
                        is_in_mapping_target,
                    )
                } else {
                    self.create_plain_notation_expression(
                        tokens,
                        notation_kind,
                        parameterizations,
                        referenced_parameterizations,
                        is_in_mapping_target,
                    )
                }
            },
        )
    }

    fn handle_notation_with_mapping_support<R>(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        notation_kind: &'a dyn NotationKind,
        scope_class: Option<ParamScopeClass>,
        data_mapping_kind: Option<&'a dyn MappingKind<dyn ParamKind>>,
        f: impl FnOnce(
            &mut RecordedTokenSlice<'a, '_, Src::Marker>,
            Option<(
                &'a dyn MappingKind<dyn ParamKind>,
                Vec<MappingSourceParam<'a>>,
                &Src::Marker,
            )>,
        ) -> Option<(R, Range<Src::Marker>)>,
    ) -> Option<(R, Range<Src::Marker>)> {
        let (notation, range) =
            self.handle_notation_with_mapping_support_impl(tokens, notation_kind, f)?;

        if let Some(scope_class) = scope_class {
            let range_class = if data_mapping_kind.is_some() {
                RangeClass::ParamRef(scope_class)
            } else {
                RangeClass::ParamNotation(scope_class)
            };
            self.source.range(range_class, &range.start..&range.end);
        }

        Some((notation, range))
    }

    fn handle_notation_with_mapping_support_impl<R>(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        notation_kind: &'a dyn NotationKind,
        f: impl FnOnce(
            &mut RecordedTokenSlice<'a, '_, Src::Marker>,
            Option<(
                &'a dyn MappingKind<dyn ParamKind>,
                Vec<MappingSourceParam<'a>>,
                &Src::Marker,
            )>,
        ) -> Option<(R, Range<Src::Marker>)>,
    ) -> Option<(R, Range<Src::Marker>)> {
        let mut segment_len = 0;
        let mut paren_depth = 0;
        let mut surrounding_paren = None;
        let mut start = None;

        for (idx, (event, range)) in tokens.iter().enumerate() {
            if start.is_none() {
                start = Some(range.start.clone());
            }

            match event {
                TokenEvent::Token(Token::ReservedChar(c, _, _))
                    if paren_depth == 0 && (*c == ',' || *c == ';' || *c == '.') =>
                {
                    break;
                }

                TokenEvent::Token(Token::Identifier(identifier, IdentifierType::Unquoted))
                    if paren_depth == 0 =>
                {
                    if let Some(mapping_kind) = notation_kind.mapping_kind(&identifier) {
                        match mapping_kind.notation() {
                            MappingNotation::Prefix => {
                                if idx == 0 {
                                    let (_, symbol_range) = tokens.pop_front().unwrap();
                                    let (params, params_range) = self
                                        .create_mapping_source_expressions(tokens, mapping_kind);
                                    if matches!(
                                        tokens.front(),
                                        Some((
                                            TokenEvent::Token(Token::ReservedChar('.', _, _)),
                                            _
                                        ))
                                    ) {
                                        tokens.pop_front();
                                    } else {
                                        let end =
                                            &params_range.as_ref().unwrap_or(&symbol_range).end;
                                        self.source.diagnostic(
                                            end..end,
                                            Severity::Error,
                                            format!("'.' expected"),
                                        );
                                    }
                                    let (result, range) = f(
                                        tokens,
                                        Some((mapping_kind, params, &symbol_range.start)),
                                    )?;
                                    return Some((result, start.unwrap()..range.end));
                                } else {
                                    self.source.diagnostic(
                                        &range.start..&range.end,
                                        Severity::Error,
                                        format!("',' expected"),
                                    );
                                    break;
                                }
                            }
                            MappingNotation::Infix { binder_paren } => {
                                if idx > 0 {
                                    let params: Vec<MappingSourceParam<'a>>;
                                    if Some(binder_paren) == surrounding_paren {
                                        tokens.pop_front();
                                        params = tokens.with_subslice(idx - 2, |source_tokens| {
                                            self.create_enclosed_mapping_source_expressions(
                                                source_tokens,
                                                mapping_kind,
                                            )
                                        });
                                        tokens.pop_front();
                                    } else {
                                        params = tokens.with_subslice(idx, |source_tokens| {
                                            self.create_enclosed_mapping_source_expressions(
                                                source_tokens,
                                                mapping_kind,
                                            )
                                        });
                                    };
                                    tokens.pop_front();
                                    let (result, range) = f(
                                        tokens,
                                        Some((mapping_kind, params, start.as_ref().unwrap())),
                                    )?;
                                    return Some((result, start.unwrap()..range.end));
                                }
                            }
                        }
                    }
                }

                TokenEvent::Paren(GroupEvent::Start(start_paren)) => {
                    if idx == 0 {
                        surrounding_paren = Some(*start_paren);
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

            segment_len = idx + 1;
        }

        tokens.with_subslice(segment_len, |segment_tokens| f(segment_tokens, None))
    }

    fn create_plain_notation_expression(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        notation_kind: &'a dyn NotationKind,
        parameterizations: &[&Parameterization<'a>],
        referenced_parameterizations: &mut [bool],
        is_in_mapping_target: bool,
    ) -> Option<(NotationExpression<'a>, Range<Src::Marker>)> {
        let mut current_sequence = Vec::new();
        let mut start = None;
        let mut end = None;

        while let Some((event, mut range)) = tokens.pop_front() {
            if start.is_none() {
                start = Some(range.start.clone());
            }

            match event {
                TokenEvent::Token(Token::ReservedChar(c, _, _)) if is_script_separator_char(c) => {
                    current_sequence.push(NotationExpression::ReservedChar(c));
                }
                TokenEvent::Token(Token::Identifier(identifier, _)) => {
                    let mut notation = NotationExpression::Identifier(identifier);
                    self.identify_notation(
                        &mut notation,
                        &range,
                        parameterizations,
                        referenced_parameterizations,
                    );
                    current_sequence.push(notation);
                }
                TokenEvent::Paren(GroupEvent::Start(start_paren)) => {
                    let mut items = Vec::new();
                    range = loop {
                        let prev_len = tokens.len();
                        if let Some((item, _)) = self.create_notation_expression(
                            tokens,
                            notation_kind,
                            None,
                            None,
                            parameterizations,
                            referenced_parameterizations,
                            is_in_mapping_target,
                        ) {
                            items.push(item);
                        }
                        let item_read = tokens.len() < prev_len;
                        let (event, range) = tokens.front().unwrap();
                        match event {
                            TokenEvent::Paren(GroupEvent::End) => {
                                let (_, range) = tokens.pop_front().unwrap();
                                break range;
                            }
                            TokenEvent::Token(Token::ReservedChar(',', _, _)) => {
                                if !item_read {
                                    self.source.diagnostic(
                                        &range.start..&range.end,
                                        Severity::Error,
                                        format!("superfluous comma"),
                                    );
                                }
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
                            _ => {}
                        }
                    };
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
        } else {
            let range = start.unwrap()..end.unwrap();
            if current_sequence.len() == 1 {
                Some((current_sequence.pop().unwrap(), range))
            } else {
                let mut notation = NotationExpression::Sequence(current_sequence);
                self.identify_notation(
                    &mut notation,
                    &range,
                    parameterizations,
                    referenced_parameterizations,
                );
                Some((notation, range))
            }
        }
    }

    fn identify_notation(
        &self,
        notation: &mut NotationExpression<'a>,
        range: &Range<Src::Marker>,
        parameterizations: &[&Parameterization<'a>],
        referenced_parameterizations: &mut [bool],
    ) {
        // Note: If the expression already references a parameter, then looking for it within
        // `parameterizations` is incorrect here, as the parameters that are referenced _within_
        // `parameterizations` come from a different scope.
        if !notation.contains_param() {
            if let Some((param_idx, _)) = notation.find_in(parameterizations) {
                self.report_param_ref(
                    param_idx,
                    &range.start..&range.end,
                    referenced_parameterizations,
                );
                *notation = NotationExpression::Param(param_idx, None);
            }
        }
    }

    fn report_param_ref(
        &self,
        param_idx: u32,
        range: Range<&Src::Marker>,
        referenced_parameterizations: &mut [bool],
    ) {
        if referenced_parameterizations[param_idx as usize] {
            self.source.diagnostic(
                range.clone(),
                Severity::Error,
                format!("parameter referenced multiple times in notation"),
            );
        } else {
            referenced_parameterizations[param_idx as usize] = true;
        }
        self.source
            .range(RangeClass::ParamRef(ParamScopeClass::Local), range);
    }

    fn create_mapping_source_param(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        mapping_kind: &'a dyn MappingKind<dyn ParamKind>,
    ) -> Option<(MappingSourceParam<'a>, Range<Src::Marker>)> {
        let notation_kind = mapping_kind.param_kind().notation_kind()?;

        self.handle_notation_with_mapping_support(
            tokens,
            notation_kind,
            Some(ParamScopeClass::Local),
            None,
            |tokens, mapping| {
                if let Some((mapping_kind, params, _)) = mapping {
                    if let Some((notation, range)) = self.create_mapping_target_notation_expression(
                        tokens,
                        mapping_kind,
                        &params,
                    ) {
                        let source_notations = params
                            .iter()
                            .map(|param| param.param.notation.clone())
                            .collect();
                        Some((
                            MappingSourceParam {
                                mapping: Some(MappingSourceParameterization {
                                    mapping_kind,
                                    source_params: params,
                                }),
                                param: Parameterization {
                                    notation,
                                    source_notations,
                                },
                            },
                            range,
                        ))
                    } else {
                        None
                    }
                } else {
                    if let Some((notation, range)) = self.create_plain_notation_expression(
                        tokens,
                        notation_kind,
                        &[],
                        &mut [],
                        false,
                    ) {
                        Some((
                            MappingSourceParam {
                                mapping: None,
                                param: Parameterization {
                                    notation,
                                    source_notations: Vec::new(),
                                },
                            },
                            range,
                        ))
                    } else {
                        None
                    }
                }
            },
        )
    }

    fn create_mapping_source_expressions(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        mapping_kind: &'a dyn MappingKind<dyn ParamKind>,
    ) -> (Vec<MappingSourceParam<'a>>, Option<Range<Src::Marker>>) {
        let mut params = Vec::new();
        let mut start = None;
        let mut end = None;

        loop {
            let prev_len = tokens.len();
            if let Some((param, range)) = self.create_mapping_source_param(tokens, mapping_kind) {
                if start.is_none() {
                    start = Some(range.start);
                }
                end = Some(range.end);
                params.push(param);
            } else {
                break;
            }
            let item_read = tokens.len() < prev_len;
            if let Some((event, range)) = tokens.front() {
                match event {
                    TokenEvent::Token(Token::ReservedChar(',', _, _)) => {
                        if !item_read {
                            self.source.diagnostic(
                                &range.start..&range.end,
                                Severity::Error,
                                format!("superfluous comma"),
                            );
                        }
                        let (_, range) = tokens.pop_front().unwrap();
                        end = Some(range.end);
                    }
                    TokenEvent::Token(Token::ReservedChar(';', _, _)) => {
                        self.source.diagnostic(
                            &range.start..&range.end,
                            Severity::Error,
                            format!("expected comma instead of semicolon"),
                        );
                        let (_, range) = tokens.pop_front().unwrap();
                        end = Some(range.end);
                    }
                    _ => break,
                }
            } else {
                break;
            }
        }

        let range = if let (Some(start), Some(end)) = (start, end) {
            Some(start..end)
        } else {
            None
        };
        (params, range)
    }

    fn create_enclosed_mapping_source_expressions(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        mapping_kind: &'a dyn MappingKind<dyn ParamKind>,
    ) -> Vec<MappingSourceParam<'a>> {
        let (params, _) = self.create_mapping_source_expressions(tokens, mapping_kind);
        if let Some((_, range)) = tokens.pop_front() {
            self.source.diagnostic(
                &range.start..&range.end,
                Severity::Error,
                format!("unexpected token in mapping source"),
            );
            while tokens.pop_front().is_some() {}
        }
        params
    }

    fn create_mapping_target_notation_expression(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        mapping_kind: &'a dyn MappingKind<dyn ParamKind>,
        params: &Vec<MappingSourceParam<'a>>,
    ) -> Option<(NotationExpression<'a>, Range<Src::Marker>)> {
        let target_notation_kind = mapping_kind.target_kind().notation_kind()?;
        self.create_notation_expression(
            tokens,
            target_notation_kind,
            None,
            None,
            &MappingSourceParam::to_parameterization_refs(params),
            &mut vec![false; params.len()],
            true,
        )
    }

    fn create_mapping_target_expression(
        &self,
        tokens: &mut RecordedTokenSlice<'a, '_, Src::Marker>,
        mapping_kind: &'a dyn MappingKind<dyn ParamKind>,
        parameterizations: &[&Parameterization<'a>],
        referenced_parameterizations: &mut [bool],
        params: Vec<MappingSourceParam<'a>>,
        mapping_start: &Src::Marker,
        is_nested_mapping_target: bool,
    ) -> Option<(NotationExpression<'a>, Range<Src::Marker>)> {
        let (notation, range) =
            self.create_mapping_target_notation_expression(tokens, mapping_kind, &params)?;
        if let Some((param_idx, param)) = notation.find_in(parameterizations) {
            let source_len = params.len();
            let expected_len = param.source_notations.len();
            if params.len() != expected_len {
                self.source.diagnostic(
                    mapping_start..&range.end,
                    Severity::Error,
                    format!("mapping target is parameterized by {expected_len} parameter(s), but mapping source contains {source_len} parameter(s)"),
                );
            } else if !params
                .iter()
                .map(|param| &param.param.notation)
                .eq(&param.source_notations)
            {
                self.source.diagnostic(
                    mapping_start..&range.end,
                    Severity::Warning,
                    format!("mapping source notation does not match original parameterization"),
                );
            }
            let notation_parameterization = NotationParameterization {
                mapping_kind,
                source_params: MappingSourceParam::to_notation_parameterizations(&params),
            };
            let identified_notation =
                NotationExpression::Param(param_idx, Some(notation_parameterization));
            let ref_start = if is_nested_mapping_target {
                mapping_start
            } else {
                &range.start
            };
            self.report_param_ref(
                param_idx,
                ref_start..&range.end,
                referenced_parameterizations,
            );
            Some((identified_notation, range))
        } else {
            self.source.diagnostic(
                &range.start..&range.end,
                Severity::Error,
                format!("mapping target must match notation of a parameter"),
            );
            None
        }
    }

    fn param_data_event<'b>(
        &self,
        state: &mut ParamDataState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        data_kind: Option<&'a dyn DataKind>,
        separator: Option<char>,
        additional_separator: Option<char>,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        match state {
            DataState::TopLevel(top_level_state) => {
                let (result, mapping_kind) = self.plain_data_event(
                    top_level_state,
                    event,
                    range.clone(),
                    out,
                    data_kind,
                    separator,
                    additional_separator,
                );
                if let Some(mapping_kind) = mapping_kind {
                    out(
                        ParameterEvent::Mapping(GroupEvent::Start(mapping_kind)),
                        &range.start..&range.start,
                    );
                    *state = DataState::Mapping(mapping_kind, MappingState::new(range.end.clone()));
                }
                result
            }

            DataState::Mapping(mapping_kind, mapping_state) => {
                let end = range.end;

                match &mut mapping_state.part_state {
                    MappingPartState::Source(param_state) => {
                        if let Some((event, range)) = self.mapping_param_event(
                            param_state,
                            event,
                            range,
                            out,
                            mapping_kind.param_kind(),
                            separator,
                            Some('.'),
                            &mut None,
                        ) {
                            if matches!(
                                event,
                                Some(TokenEvent::Token(Token::ReservedChar('.', _, _)))
                            ) {
                                mapping_state.part_state =
                                    MappingPartState::Target(Box::new(ParamDataState::new()));
                            } else if !matches!(
                                event,
                                Some(TokenEvent::Token(Token::ReservedChar(',', _, _)))
                            ) {
                                self.source.diagnostic(
                                    range.start..range.start,
                                    Severity::Error,
                                    format!("'.' expected"),
                                );
                                out(
                                    ParameterEvent::Mapping(GroupEvent::End),
                                    &mapping_state.end_marker..&mapping_state.end_marker,
                                );
                                *state = ParamDataState::new();
                                return Some((event, range));
                            }
                        }
                    }

                    MappingPartState::Target(data_state) => {
                        let result = self.param_data_event(
                            data_state,
                            event,
                            range,
                            out,
                            Some(mapping_kind.target_kind()),
                            separator,
                            additional_separator,
                        );
                        if result.is_some() {
                            out(
                                ParameterEvent::Mapping(GroupEvent::End),
                                &mapping_state.end_marker..&mapping_state.end_marker,
                            );
                            *state = ParamDataState::new();
                            return result;
                        }
                    }
                }

                mapping_state.end_marker = end.clone();
                None
            }
        }
    }

    fn plain_data_event<'b>(
        &self,
        state: &mut PlainDataState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        data_kind: Option<&'a dyn DataKind>,
        separator: Option<char>,
        additional_separator: Option<char>,
    ) -> (
        Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)>,
        Option<&'a dyn MappingKind<dyn DataKind>>,
    ) {
        match state {
            PlainDataState::TopLevel { has_contents } => {
                match &event {
                    Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                        if *c == ','
                            || *c == ';'
                            || Some(*c) == separator
                            || Some(*c) == additional_separator =>
                    {
                        return (Some((event, range)), None);
                    }
                    Some(TokenEvent::Token(Token::Identifier(
                        identifier,
                        IdentifierType::Unquoted,
                    ))) => {
                        if let Some(data_kind) = data_kind {
                            if let Some(mapping_kind) = data_kind.mapping_kind(identifier) {
                                if matches!(mapping_kind.notation(), MappingNotation::Prefix) {
                                    return (None, Some(mapping_kind));
                                }
                            }
                        }
                    }
                    Some(TokenEvent::Paren(GroupEvent::Start(start_paren))) => {
                        if let Some(data_kind) = data_kind {
                            if let Some(special_data_kind) =
                                data_kind.special_data_kind(*start_paren)
                            {
                                out(
                                    ParameterEvent::SpecialData(GroupEvent::Start(
                                        special_data_kind,
                                    )),
                                    range,
                                );
                                *state = PlainDataState::Special(
                                    special_data_kind,
                                    EnclosedDataState::new(),
                                );
                                return (None, None);
                            }
                            if let Some(object_kind) = data_kind.object_kind(*start_paren) {
                                out(
                                    ParameterEvent::Object(GroupEvent::Start(object_kind)),
                                    range,
                                );
                                *state = PlainDataState::Object(object_kind, ObjectState::new());
                                return (None, None);
                            }
                        }
                        out(ParameterEvent::Token(event.unwrap()), range);
                        *state = PlainDataState::Paren(EnclosedDataState::new());
                        return (None, None);
                    }
                    Some(TokenEvent::Paren(GroupEvent::End)) | None => {
                        return (Some((event, range)), None);
                    }
                    _ => {}
                }

                out(ParameterEvent::Token(event.unwrap()), range);
                *has_contents = true;
            }

            PlainDataState::Paren(enclosed_data_state) => {
                if let Some((event, range)) = self.enclosed_data_event(
                    enclosed_data_state,
                    event,
                    range,
                    out,
                    data_kind,
                    None,
                ) {
                    if matches!(event, Some(TokenEvent::Paren(GroupEvent::End))) {
                        out(ParameterEvent::Token(event.unwrap()), range);
                        *state = PlainDataState::TopLevel { has_contents: true };
                    } else {
                        out(ParameterEvent::Token(event.unwrap()), range);
                    }
                }
            }

            PlainDataState::Special(special_data_kind, enclosed_data_state) => {
                if let Some((event, range)) = self.enclosed_data_event(
                    enclosed_data_state,
                    event,
                    range,
                    out,
                    Some(*special_data_kind),
                    None,
                ) {
                    if matches!(event, Some(TokenEvent::Paren(GroupEvent::End))) {
                        out(ParameterEvent::SpecialData(GroupEvent::End), range);
                        *state = PlainDataState::TopLevel { has_contents: true };
                    } else {
                        out(ParameterEvent::Token(event.unwrap()), range);
                    }
                }
            }

            PlainDataState::Object(object_kind, object_state) => {
                if let Some((_, range)) =
                    self.object_event(object_state, event, range, out, *object_kind)
                {
                    out(ParameterEvent::Object(GroupEvent::End), range);
                    *state = PlainDataState::TopLevel { has_contents: true };
                }
            }
        }

        (None, None)
    }

    fn output_plain_data(
        &self,
        tokens: &mut RecordedTokens<'a, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        data_kind: Option<&'a dyn DataKind>,
    ) {
        let mut state = PlainDataState::TopLevel {
            has_contents: false,
        };

        while let Some((event, range)) = tokens.pop_front() {
            let (result, mapping_kind) = self.plain_data_event(
                &mut state,
                Some(event),
                &range.start..&range.end,
                out,
                data_kind,
                None,
                None,
            );
            assert!(result.is_none());
            assert!(mapping_kind.is_none());
        }

        assert!(matches!(
            state,
            PlainDataState::TopLevel { has_contents: _ }
        ));
    }

    fn enclosed_data_event<'b>(
        &self,
        state: &mut EnclosedDataState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        data_kind: Option<&'a dyn DataKind>,
        separator: Option<char>,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        match state {
            DataState::TopLevel(top_level_state) => {
                if top_level_state.paren_depth == 0 {
                    match &event {
                        Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                            if *c == ',' || *c == ';' || Some(*c) == separator =>
                        {
                            top_level_state.surrounding_paren = None;
                            self.output_plain_data(
                                &mut top_level_state.recorded_tokens,
                                out,
                                data_kind,
                            );
                            return Some((event, range));
                        }
                        Some(TokenEvent::Token(Token::Identifier(
                            identifier,
                            IdentifierType::Unquoted,
                        ))) => {
                            if let Some(data_kind) = data_kind {
                                if let Some(mapping_kind) = data_kind.mapping_kind(identifier) {
                                    let notation = mapping_kind.notation();
                                    if let MappingNotation::Prefix = notation {
                                        self.output_plain_data(
                                            &mut top_level_state.recorded_tokens,
                                            out,
                                            Some(data_kind),
                                        );
                                    }
                                    out(
                                        ParameterEvent::Mapping(GroupEvent::Start(mapping_kind)),
                                        &range.start..&range.start,
                                    );
                                    let mut mapping_state = MappingState::new(range.end.clone());
                                    if let MappingNotation::Infix { binder_paren } = notation {
                                        if top_level_state.surrounding_paren == Some(binder_paren) {
                                            top_level_state.recorded_tokens.pop_front();
                                            top_level_state.recorded_tokens.pop_back();
                                        }
                                        self.output_mapping_source(
                                            &mut top_level_state.recorded_tokens,
                                            out,
                                            mapping_kind.param_kind(),
                                            &mut None,
                                        );
                                        mapping_state.part_state = MappingPartState::Target(
                                            Box::new(EnclosedDataState::new()),
                                        );
                                    }
                                    *state = DataState::Mapping(mapping_kind, mapping_state);
                                    return None;
                                }
                            }
                        }
                        _ => {}
                    }

                    top_level_state.surrounding_paren = None;
                }

                match &event {
                    Some(TokenEvent::Paren(GroupEvent::Start(start_paren))) => {
                        if top_level_state.recorded_tokens.is_empty() {
                            top_level_state.surrounding_paren = Some(*start_paren);
                        }
                        top_level_state.paren_depth += 1;
                    }
                    Some(TokenEvent::Paren(GroupEvent::End)) | None => {
                        if top_level_state.paren_depth > 0 {
                            top_level_state.paren_depth -= 1;
                        } else {
                            self.output_plain_data(
                                &mut top_level_state.recorded_tokens,
                                out,
                                data_kind,
                            );
                            return Some((event, range));
                        }
                    }
                    _ => {}
                }

                top_level_state
                    .recorded_tokens
                    .push_back((event.unwrap(), range.start.clone()..range.end.clone()));
            }

            DataState::Mapping(mapping_kind, mapping_state) => {
                let end = range.end;

                match &mut mapping_state.part_state {
                    MappingPartState::Source(param_state) => {
                        if let Some((event, range)) = self.mapping_param_event(
                            param_state,
                            event,
                            range,
                            out,
                            mapping_kind.param_kind(),
                            separator,
                            Some('.'),
                            &mut None,
                        ) {
                            if matches!(
                                event,
                                Some(TokenEvent::Token(Token::ReservedChar('.', _, _)))
                            ) {
                                mapping_state.part_state =
                                    MappingPartState::Target(Box::new(EnclosedDataState::new()));
                            } else if !matches!(
                                event,
                                Some(TokenEvent::Token(Token::ReservedChar(',', _, _)))
                            ) {
                                self.source.diagnostic(
                                    range.start..range.start,
                                    Severity::Error,
                                    format!("'.' expected"),
                                );
                                out(
                                    ParameterEvent::Mapping(GroupEvent::End),
                                    &mapping_state.end_marker..&mapping_state.end_marker,
                                );
                                *state = EnclosedDataState::new();
                                return Some((event, range));
                            }
                        }
                    }

                    MappingPartState::Target(data_state) => {
                        let result = self.enclosed_data_event(
                            data_state,
                            event,
                            range,
                            out,
                            Some(mapping_kind.target_kind()),
                            separator,
                        );
                        if result.is_some() {
                            out(
                                ParameterEvent::Mapping(GroupEvent::End),
                                &mapping_state.end_marker..&mapping_state.end_marker,
                            );
                            *state = EnclosedDataState::new();
                            return result;
                        }
                    }
                }

                mapping_state.end_marker = end.clone();
            }
        }

        None
    }

    fn mapping_param_event<'b>(
        &self,
        state: &mut MappingParamState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        separator: Option<char>,
        additional_separator: Option<char>,
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        match state {
            MappingParamState::TopLevel(top_level_state) => {
                if top_level_state.paren_depth == 0 {
                    match &event {
                        Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                            if *c == ','
                                || *c == ';'
                                || Some(*c) == separator
                                || Some(*c) == additional_separator =>
                        {
                            top_level_state.surrounding_paren = None;
                            if top_level_state.recorded_tokens.is_empty() {
                                if *c == ',' {
                                    self.source.diagnostic(
                                        range.clone(),
                                        Severity::Error,
                                        format!("superfluous comma"),
                                    );
                                }
                            } else {
                                self.output_plain_mapping_param(
                                    &mut top_level_state.recorded_tokens,
                                    out,
                                    param_kind,
                                    result_params,
                                );
                            }
                            return Some((event, range));
                        }
                        Some(TokenEvent::Token(Token::Identifier(
                            identifier,
                            IdentifierType::Unquoted,
                        ))) => {
                            if let Some(notation_kind) = param_kind.notation_kind() {
                                if let Some(mapping_kind) = notation_kind.mapping_kind(identifier) {
                                    let notation = mapping_kind.notation();
                                    if let MappingNotation::Prefix = notation {
                                        if !top_level_state.recorded_tokens.is_empty() {
                                            self.output_plain_mapping_param(
                                                &mut top_level_state.recorded_tokens,
                                                out,
                                                param_kind,
                                                result_params,
                                            );
                                            self.source.diagnostic(
                                                &range.start..&range.start,
                                                Severity::Error,
                                                format!("',' expected"),
                                            );
                                        }
                                    }
                                    out(
                                        ParameterEvent::MappingParam(GroupEvent::Start(Some(
                                            mapping_kind,
                                        ))),
                                        &range.start..&range.start,
                                    );
                                    let mut mapping_state =
                                        MappingParamMappingState::new(range.end.clone());
                                    if let MappingNotation::Infix { binder_paren } = notation {
                                        if top_level_state.surrounding_paren == Some(binder_paren) {
                                            top_level_state.recorded_tokens.pop_front();
                                            top_level_state.recorded_tokens.pop_back();
                                        }
                                        self.output_mapping_source(
                                            &mut top_level_state.recorded_tokens,
                                            out,
                                            mapping_kind.param_kind(),
                                            &mut mapping_state.params,
                                        );
                                        mapping_state.part_state =
                                            MappingPartState::Target(Box::new(ParamState::new()));
                                    }
                                    *state =
                                        MappingParamState::Mapping(mapping_kind, mapping_state);
                                    return None;
                                }
                            }
                        }
                        _ => {}
                    }

                    top_level_state.surrounding_paren = None;
                }

                match &event {
                    Some(TokenEvent::Paren(GroupEvent::Start(start_paren))) => {
                        if top_level_state.recorded_tokens.is_empty() {
                            top_level_state.surrounding_paren = Some(*start_paren);
                        }
                        top_level_state.paren_depth += 1;
                    }
                    Some(TokenEvent::Paren(GroupEvent::End)) | None => {
                        if top_level_state.paren_depth > 0 {
                            top_level_state.paren_depth -= 1;
                        } else {
                            if !top_level_state.recorded_tokens.is_empty() {
                                self.output_plain_mapping_param(
                                    &mut top_level_state.recorded_tokens,
                                    out,
                                    param_kind,
                                    result_params,
                                );
                            }
                            return Some((event, range));
                        }
                    }
                    _ => {}
                }

                top_level_state
                    .recorded_tokens
                    .push_back((event.unwrap(), range.start.clone()..range.end.clone()));
            }

            MappingParamState::Mapping(mapping_kind, mapping_state) => {
                let end = range.end;

                match &mut mapping_state.part_state {
                    MappingPartState::Source(param_state) => {
                        if let Some((event, range)) = self.mapping_param_event(
                            param_state,
                            event,
                            range,
                            out,
                            mapping_kind.param_kind(),
                            separator,
                            Some('.'),
                            &mut mapping_state.params,
                        ) {
                            if matches!(
                                event,
                                Some(TokenEvent::Token(Token::ReservedChar('.', _, _)))
                            ) {
                                mapping_state.part_state =
                                    MappingPartState::Target(Box::new(ParamState::new()));
                            } else if !matches!(
                                event,
                                Some(TokenEvent::Token(Token::ReservedChar(',', _, _)))
                            ) {
                                self.source.diagnostic(
                                    range.start..range.start,
                                    Severity::Error,
                                    format!("'.' expected"),
                                );
                                out(
                                    ParameterEvent::MappingParam(GroupEvent::End),
                                    &mapping_state.end_marker..&mapping_state.end_marker,
                                );
                                *state = MappingParamState::new();
                                return Some((event, range));
                            }
                        }
                    }

                    MappingPartState::Target(param_state) => {
                        let result = self.param_event(
                            param_state,
                            event,
                            range,
                            out,
                            mapping_kind.target_kind(),
                            ParamScopeClass::Local,
                            separator,
                            additional_separator,
                            &[],
                            mapping_state.params.as_deref(),
                            result_params,
                        );
                        if result.is_some() {
                            out(
                                ParameterEvent::MappingParam(GroupEvent::End),
                                &mapping_state.end_marker..&mapping_state.end_marker,
                            );
                            *state = MappingParamState::new();
                            return result;
                        }
                    }
                }

                mapping_state.end_marker = end.clone();
            }
        }

        None
    }

    fn output_plain_mapping_param(
        &self,
        tokens: &mut RecordedTokens<'a, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) {
        let (_, range) = tokens.front().unwrap();
        let start = range.start.clone();
        out(
            ParameterEvent::MappingParam(GroupEvent::Start(None)),
            &start..&start,
        );
        let end = self
            .output_single_param(
                tokens,
                out,
                param_kind,
                ParamScopeClass::Local,
                &[],
                result_params,
            )
            .unwrap_or(start);
        out(ParameterEvent::MappingParam(GroupEvent::End), &end..&end);
    }

    fn output_single_param(
        &self,
        tokens: &mut RecordedTokens<'a, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        scope_class: ParamScopeClass,
        parameterizations: &[&Parameterization<'a>],
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) -> Option<Src::Marker> {
        if tokens.is_empty() {
            return None;
        }

        let mut state = ParamState::new();
        let mut end = None;

        while let Some((event, range)) = tokens.pop_front() {
            if let Some((_, range)) = self.param_event(
                &mut state,
                Some(event),
                &range.start..&range.end,
                out,
                param_kind,
                scope_class,
                None,
                None,
                parameterizations,
                None,
                result_params,
            ) {
                self.source
                    .diagnostic(range, Severity::Error, format!("unexpected delimiter"));
                return end;
            }

            end = Some(range.end);
        }

        let end_ref = end.as_ref().unwrap();
        let result = self.param_event(
            &mut state,
            None,
            end_ref..end_ref,
            out,
            param_kind,
            scope_class,
            None,
            None,
            parameterizations,
            None,
            result_params,
        );
        assert!(result.is_some());

        end
    }

    fn output_mapping_source(
        &self,
        tokens: &mut RecordedTokens<'a, Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        param_kind: &'a dyn ParamKind,
        result_params: &mut Option<Vec<Parameterization<'a>>>,
    ) {
        if tokens.is_empty() {
            return;
        }

        let mut state = MappingParamState::new();
        let mut end = None;

        while let Some((event, range)) = tokens.pop_front() {
            if let Some((event, range)) = self.mapping_param_event(
                &mut state,
                Some(event),
                &range.start..&range.end,
                out,
                param_kind,
                None,
                None,
                result_params,
            ) {
                if !matches!(
                    event,
                    Some(TokenEvent::Token(Token::ReservedChar(',', _, _)))
                ) {
                    self.source
                        .diagnostic(range, Severity::Error, format!("unexpected delimiter"));
                    return;
                }
            }

            end = Some(range.end);
        }

        let end_ref = end.as_ref().unwrap();
        let result = self.mapping_param_event(
            &mut state,
            None,
            end_ref..end_ref,
            out,
            param_kind,
            None,
            None,
            result_params,
        );
        assert!(result.is_some());
    }

    fn object_event<'b>(
        &self,
        state: &mut ObjectState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        object_kind: &'a dyn ObjectKind,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        if state.item_state.is_none() {
            match event {
                Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                    if c == object_kind.separator() =>
                {
                    self.source.diagnostic(
                        range,
                        Severity::Error,
                        format!("superfluous separator"),
                    );
                    return None;
                }
                Some(TokenEvent::Paren(GroupEvent::End)) | None => {
                    return Some((event, range));
                }
                _ => {}
            }
            out(
                ParameterEvent::ObjectItem(GroupEvent::Start(())),
                range.start..range.start,
            );
            state.item_state = Some(ObjectItemState::new(range.start.clone()));
        }

        let item_state = state.item_state.as_mut().unwrap();
        if let Some((event, range)) =
            self.object_item_event(item_state, event, range, out, object_kind)
        {
            out(
                ParameterEvent::ObjectItem(GroupEvent::End),
                &item_state.end_marker..&item_state.end_marker,
            );
            state.item_state = None;
            if matches!(event, Some(TokenEvent::Paren(GroupEvent::End)) | None) {
                return Some((event, range));
            }
        }

        None
    }

    fn object_item_event<'b>(
        &self,
        state: &mut ObjectItemState<'a, Src::Marker>,
        event: Option<TokenEvent<'a>>,
        range: Range<&'b Src::Marker>,
        out: &mut impl FnMut(ParameterEvent<'a>, Range<&Src::Marker>),
        object_kind: &'a dyn ObjectKind,
    ) -> Option<(Option<TokenEvent<'a>>, Range<&'b Src::Marker>)> {
        let separator = object_kind.separator();

        match &mut state.part_state {
            ObjectItemPartState::Notation { paren_depth } => {
                match event {
                    Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                        if *paren_depth == 0 && c == separator =>
                    {
                        state.part_state = ObjectItemPartState::Parameterization {
                            section_state: None,
                            params: None,
                        };
                        return None;
                    }
                    Some(TokenEvent::Paren(GroupEvent::Start(_))) => {
                        *paren_depth += 1;
                    }
                    Some(TokenEvent::Paren(GroupEvent::End)) | None => {
                        if *paren_depth > 0 {
                            *paren_depth -= 1;
                        } else {
                            if let Some(end) = self.output_single_param(
                                &mut state.recorded_notation_tokens,
                                out,
                                object_kind.param_kind(),
                                ParamScopeClass::Object,
                                &[],
                                &mut None,
                            ) {
                                state.end_marker = end;
                            }
                            return Some((event, range));
                        }
                    }
                    _ => {}
                }

                state
                    .recorded_notation_tokens
                    .push_back((event.unwrap(), range.start.clone()..range.end.clone()));
            }

            ObjectItemPartState::Parameterization {
                section_state,
                params,
            } => {
                let parameterization_kind = object_kind.parameterization();

                if section_state.is_none() {
                    if matches!(
                        event,
                        Some(TokenEvent::Token(Token::ReservedChar(c, _, _))) if c == separator
                    ) {
                        if let Some(end) = self.output_single_param(
                            &mut state.recorded_notation_tokens,
                            out,
                            object_kind.param_kind(),
                            ParamScopeClass::Object,
                            &[],
                            &mut None,
                        ) {
                            state.end_marker = end;
                        }
                        return Some((event, range));
                    }

                    out(
                        ParameterEvent::Parameterization(GroupEvent::Start(parameterization_kind)),
                        range.start..range.start,
                    );
                    *section_state = Some(Box::new(SectionState::Start));
                    *params = Some(Vec::new());
                }

                let end = range.end;

                if let Some((event, range)) = self.section_event(
                    section_state.as_mut().unwrap(),
                    event,
                    range,
                    out,
                    parameterization_kind,
                    ParamScopeClass::Local,
                    Some(separator),
                    &[],
                    params,
                ) {
                    out(
                        ParameterEvent::Parameterization(GroupEvent::End),
                        &end..&end,
                    );

                    self.output_single_param(
                        &mut state.recorded_notation_tokens,
                        out,
                        object_kind.param_kind(),
                        ParamScopeClass::Object,
                        &Parameterization::to_ref_slice(params.as_deref()),
                        &mut None,
                    );

                    if matches!(
                        event,
                        Some(TokenEvent::Token(Token::ReservedChar(c, _, _))) if c == separator
                    ) {
                        state.part_state = ObjectItemPartState::ExtraSection {
                            extra_section_idx: 0,
                            section_state: None,
                            superfluous_paren_depth: 0,
                        };
                        return None;
                    } else {
                        return Some((event, range));
                    }
                }

                state.end_marker = end.clone();
            }

            ObjectItemPartState::ExtraSection {
                extra_section_idx,
                section_state,
                superfluous_paren_depth,
            } => {
                if section_state.is_none() {
                    if matches!(
                        event,
                        Some(TokenEvent::Token(Token::ReservedChar(c, _, _))) if c == separator
                    ) {
                        return Some((event, range));
                    }

                    out(
                        ParameterEvent::ObjectItemExtra(GroupEvent::Start(())),
                        range.start..range.start,
                    );
                    *section_state = Some(Box::new(SectionState::Start));
                }

                let end = range.end;

                if let Some(section_kind) = object_kind.extra_section_kind(*extra_section_idx) {
                    if let Some((event, range)) = self.section_event(
                        section_state.as_mut().unwrap(),
                        event,
                        range,
                        out,
                        section_kind,
                        ParamScopeClass::Extra,
                        Some(separator),
                        &[],
                        &mut None,
                    ) {
                        out(ParameterEvent::ObjectItemExtra(GroupEvent::End), &end..&end);

                        if matches!(
                            event,
                            Some(TokenEvent::Token(Token::ReservedChar(c, _, _))) if c == separator
                        ) {
                            *extra_section_idx += 1;
                            *section_state = None;
                            return None;
                        } else {
                            return Some((event, range));
                        }
                    }
                } else {
                    match event {
                        Some(TokenEvent::Token(Token::ReservedChar(c, _, _)))
                            if *superfluous_paren_depth == 0 && c == separator =>
                        {
                            out(ParameterEvent::ObjectItemExtra(GroupEvent::End), &end..&end);
                            *extra_section_idx += 1;
                            *section_state = None;
                            return None;
                        }
                        Some(TokenEvent::Paren(GroupEvent::Start(_))) => {
                            *superfluous_paren_depth += 1;
                        }
                        Some(TokenEvent::Paren(GroupEvent::End)) | None => {
                            if *superfluous_paren_depth > 0 {
                                *superfluous_paren_depth -= 1;
                            } else {
                                out(ParameterEvent::ObjectItemExtra(GroupEvent::End), &end..&end);
                                return Some((event, range));
                            }
                        }
                        _ => {}
                    }
                }

                state.end_marker = end.clone();
            }
        }

        None
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
        param_state: ParamState<'a, Marker>,
        end_marker: Marker,
    },
    Subsection(&'a dyn SectionKind, Box<SectionState<'a, Marker>>),
    AfterSubsection,
}

#[derive(Clone, PartialEq)]
pub enum ParamState<'a, Marker: Clone + PartialEq> {
    Notation(ParamNotationState<'a, Marker>),
    Data(ParamDataState<'a, Marker>),
}

impl<'a, Marker: Clone + PartialEq> ParamState<'a, Marker> {
    fn new() -> Self {
        ParamState::Notation(ParamNotationState::new())
    }
}

#[derive(Clone, PartialEq)]
pub struct ParamNotationState<'a, Marker: Clone + PartialEq> {
    recorded_tokens: RecordedTokens<'a, Marker>,
    notation_len: usize,
    mapping_state: ParamNotationMappingAnalysisState<'a>,
}

impl<'a, Marker: Clone + PartialEq> ParamNotationState<'a, Marker> {
    fn new() -> Self {
        ParamNotationState {
            recorded_tokens: RecordedTokens::new(),
            notation_len: 0,
            mapping_state: ParamNotationMappingAnalysisState::new(),
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum ParamNotationMappingAnalysisState<'a> {
    TopLevel {
        paren_depth: u32,
    },
    PrefixMapping(
        &'a dyn MappingKind<dyn ParamKind>,
        ParamNotationMappingState<'a>,
    ),
}

impl<'a> ParamNotationMappingAnalysisState<'a> {
    fn new() -> Self {
        ParamNotationMappingAnalysisState::TopLevel { paren_depth: 0 }
    }
}

#[derive(Clone, PartialEq)]
pub enum ParamNotationMappingState<'a> {
    Source(Box<ParamNotationMappingAnalysisState<'a>>),
    Target(Box<ParamNotationMappingAnalysisState<'a>>),
}

#[derive(Clone, PartialEq)]
pub enum DataState<'a, Marker: Clone + PartialEq, TopLevelState> {
    TopLevel(TopLevelState),
    Mapping(
        &'a dyn MappingKind<dyn DataKind>,
        MappingState<'a, Marker, TopLevelState>,
    ),
}

#[derive(Clone, PartialEq)]
pub enum PlainDataState<'a, Marker: Clone + PartialEq> {
    TopLevel { has_contents: bool },
    Paren(EnclosedDataState<'a, Marker>),
    Special(&'a dyn DataKind, EnclosedDataState<'a, Marker>),
    Object(&'a dyn ObjectKind, ObjectState<'a, Marker>),
}

pub type ParamDataState<'a, Marker> = DataState<'a, Marker, PlainDataState<'a, Marker>>;

impl<'a, Marker: Clone + PartialEq> ParamDataState<'a, Marker> {
    fn new() -> Self {
        DataState::TopLevel(PlainDataState::TopLevel {
            has_contents: false,
        })
    }
}

#[derive(Clone, PartialEq)]
pub struct MappingAnalysisState<'a, Marker: Clone + PartialEq> {
    recorded_tokens: RecordedTokens<'a, Marker>,
    paren_depth: u32,
    surrounding_paren: Option<char>,
}

impl<'a, Marker: Clone + PartialEq> MappingAnalysisState<'a, Marker> {
    fn new() -> Self {
        MappingAnalysisState {
            recorded_tokens: RecordedTokens::new(),
            paren_depth: 0,
            surrounding_paren: None,
        }
    }
}

pub type EnclosedDataState<'a, Marker> = DataState<'a, Marker, MappingAnalysisState<'a, Marker>>;

impl<'a, Marker: Clone + PartialEq> EnclosedDataState<'a, Marker> {
    fn new() -> Self {
        DataState::TopLevel(MappingAnalysisState::new())
    }
}

#[derive(Clone, PartialEq)]
pub struct ObjectState<'a, Marker: Clone + PartialEq> {
    item_state: Option<ObjectItemState<'a, Marker>>,
}

impl<'a, Marker: Clone + PartialEq> ObjectState<'a, Marker> {
    fn new() -> Self {
        ObjectState { item_state: None }
    }
}

#[derive(Clone, PartialEq)]
pub struct ObjectItemState<'a, Marker: Clone + PartialEq> {
    part_state: ObjectItemPartState<'a, Marker>,
    recorded_notation_tokens: RecordedTokens<'a, Marker>,
    end_marker: Marker,
}

impl<'a, Marker: Clone + PartialEq> ObjectItemState<'a, Marker> {
    fn new(end_marker: Marker) -> Self {
        ObjectItemState {
            part_state: ObjectItemPartState::Notation { paren_depth: 0 },
            recorded_notation_tokens: RecordedTokens::new(),
            end_marker,
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum ObjectItemPartState<'a, Marker: Clone + PartialEq> {
    Notation {
        paren_depth: u32,
    },
    Parameterization {
        section_state: Option<Box<SectionState<'a, Marker>>>,
        params: Option<Vec<Parameterization<'a>>>,
    },
    ExtraSection {
        extra_section_idx: u32,
        section_state: Option<Box<SectionState<'a, Marker>>>,
        superfluous_paren_depth: u32,
    },
}

#[derive(Clone, PartialEq)]
pub struct MappingState<'a, Marker: Clone + PartialEq, TopLevelState> {
    part_state: MappingPartState<'a, Marker, DataState<'a, Marker, TopLevelState>>,
    end_marker: Marker,
}

impl<'a, Marker: Clone + PartialEq, TopLevelState> MappingState<'a, Marker, TopLevelState> {
    fn new(end_marker: Marker) -> Self {
        MappingState {
            part_state: MappingPartState::Source(Box::new(MappingParamState::new())),
            end_marker,
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum MappingPartState<'a, Marker: Clone + PartialEq, TargetState> {
    Source(Box<MappingParamState<'a, Marker>>),
    Target(Box<TargetState>),
}

#[derive(Clone, PartialEq)]
pub enum MappingParamState<'a, Marker: Clone + PartialEq> {
    TopLevel(MappingAnalysisState<'a, Marker>),
    Mapping(
        &'a dyn MappingKind<dyn ParamKind>,
        MappingParamMappingState<'a, Marker>,
    ),
}

impl<'a, Marker: Clone + PartialEq> MappingParamState<'a, Marker> {
    fn new() -> Self {
        MappingParamState::TopLevel(MappingAnalysisState::new())
    }
}

#[derive(Clone, PartialEq)]
pub struct MappingParamMappingState<'a, Marker: Clone + PartialEq> {
    part_state: MappingPartState<'a, Marker, ParamState<'a, Marker>>,
    params: Option<Vec<Parameterization<'a>>>,
    end_marker: Marker,
}

impl<'a, Marker: Clone + PartialEq> MappingParamMappingState<'a, Marker> {
    fn new(end_marker: Marker) -> Self {
        MappingParamMappingState {
            part_state: MappingPartState::Source(Box::new(MappingParamState::new())),
            params: Some(Vec::new()),
            end_marker,
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct Parameterization<'a> {
    notation: NotationExpression<'a>,
    source_notations: Vec<NotationExpression<'a>>,
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

    fn to_ref_slice<'b, 'c>(params: Option<&'b [Self]>) -> Cow<'c, [&'b Self]> {
        Self::concat(&[], params)
    }
}

#[derive(Clone, PartialEq)]
pub struct MappingSourceParam<'a> {
    mapping: Option<MappingSourceParameterization<'a>>,
    param: Parameterization<'a>,
}

impl<'a> MappingSourceParam<'a> {
    fn to_parameterization_refs<'b>(params: &'b [Self]) -> Vec<&'b Parameterization<'a>> {
        params.iter().map(|param| &param.param).collect()
    }

    fn to_notation_parameterization(&self) -> Option<NotationParameterization<'a>> {
        self.mapping
            .as_ref()
            .map(MappingSourceParameterization::to_notation_parameterization)
    }

    fn to_notation_parameterizations(params: &[Self]) -> Vec<Option<NotationParameterization<'a>>> {
        params
            .iter()
            .map(Self::to_notation_parameterization)
            .collect()
    }
}

#[derive(Clone, PartialEq)]
pub struct MappingSourceParameterization<'a> {
    mapping_kind: &'a dyn MappingKind<dyn ParamKind>,
    source_params: Vec<MappingSourceParam<'a>>,
}

impl<'a> MappingSourceParameterization<'a> {
    fn to_notation_parameterization(&self) -> NotationParameterization<'a> {
        NotationParameterization {
            mapping_kind: self.mapping_kind,
            source_params: MappingSourceParam::to_notation_parameterizations(&self.source_params),
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

    use crate::{layer1_tokenizer::*, metamodel::test_helpers::*};

    use super::*;

    #[test]
    fn globals() -> Result<(), Message> {
        let metamodel = TestMetaModel::new();
        test_parameter_identification(
            "%slate \"test\";",
            &metamodel,
            Vec::new(),
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(" : T;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(" : T := y;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(". T;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(RangeClass::Paren, vec![RangeClassTreeNode::Text("⎿T⏌")]),
                RangeClassTreeNode::Text(" := y;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Range(
                        RangeClass::Paren,
                        vec![RangeClassTreeNode::Text("(x)")],
                    )],
                ),
                RangeClassTreeNode::Text(" : T := y;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamRef(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(" ↦ y;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![RangeClassTreeNode::Text("(x : T)")],
                ),
                RangeClassTreeNode::Text(" := y;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(" : T; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("y")],
                ),
                RangeClassTreeNode::Text(" : U;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x y")],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x^y_z")],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x y")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%z")],
                ),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![RangeClassTreeNode::Text("(a;b)")],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("x"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("()")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("x"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("(,)")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("x"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("(y,z)")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("x"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("(y,z,)")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("x"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("(,y,z,)")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("x"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("(y,,z,)")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("x"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("(y,z,,)")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                range_text: ";".into(),
                severity: Severity::Error,
                msg: "expected comma instead of semicolon".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("x"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("(y;z)")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; x(42);",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("x".into()),
                    }],
                    vec![DataToken::Paren(
                        '(',
                        vec![DataToken::Token(Token::Number("42".into()))],
                    )],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Number,
                            vec![RangeClassTreeNode::Text("42")],
                        ),
                        RangeClassTreeNode::Text(")"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(","),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("y")],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(","),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("y")],
                ),
                RangeClassTreeNode::Text(" : T;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(",,"),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("y")],
                ),
                RangeClassTreeNode::Text(" : T;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; 42;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    Vec::new(),
                    vec![DataToken::Token(Token::Number("42".into()))],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(RangeClass::Number, vec![RangeClassTreeNode::Text("42")]),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        Ok(())
    }

    #[test]
    fn parameterizations() -> Result<(), Message> {
        let metamodel = TestMetaModel::new();
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
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
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(0, None)],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [b c : B] a(b c) : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: Vec::new(),
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Identifier("c".into()),
                                ]),
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
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(0, None)],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b c")],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b c")],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [b,c : B] b + c : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: Vec::new(),
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
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Param(0, None),
                            NotationExpression::Identifier("+".into()),
                            NotationExpression::Param(1, None),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(","),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("c")],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(" + "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("c")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" : D]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(","),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("c")],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" : D]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text("; "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("c")],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" : D]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(" : B, "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("c")],
                        ),
                        RangeClassTreeNode::Text(" : C]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [a] a;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: Vec::new(),
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Identifier("a".into()),
                            }],
                            Vec::new(),
                        ),
                    }],
                )],
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Param(0, None),
                    }],
                    Vec::new(),
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "a".into(),
                severity: Severity::Error,
                msg: "notation cannot consist entirely of a parameter".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text("]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Range(
                        RangeClass::ParamRef(ParamScopeClass::Local),
                        vec![RangeClassTreeNode::Text("a")],
                    )],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [a] (a) a;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: Vec::new(),
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Identifier("a".into()),
                            }],
                            Vec::new(),
                        ),
                    }],
                )],
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Sequence(vec![
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(0, None)],
                            ),
                            NotationExpression::Param(0, None),
                        ]),
                    }],
                    Vec::new(),
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "a".into(),
                severity: Severity::Error,
                msg: "parameter referenced multiple times in notation".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text("]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        Ok(())
    }

    #[test]
    fn higher_order_parameterizations() -> Result<(), Message> {
        let metamodel = TestMetaModel::new();
        test_parameter_identification(
            "%slate \"test\"; [b : B] λ. b : A;",
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
                        notation: NotationExpression::Param(
                            0,
                            Some(NotationParameterization {
                                mapping_kind: &metamodel,
                                source_params: Vec::new(),
                            }),
                        ),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("λ. "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [b : B] a(() ↦ b) : A;",
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
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(
                                    0,
                                    Some(NotationParameterization {
                                        mapping_kind: metamodel
                                            .opposite_mapping
                                            .as_ref()
                                            .unwrap()
                                            .as_ref(),
                                        source_params: vec![],
                                    }),
                                )],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![RangeClassTreeNode::Text("()")],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[c : C] b(c) : B] λ c. b(c) : A;",
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
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0, None)],
                                    ),
                                ]),
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
                        notation: NotationExpression::Param(
                            0,
                            Some(NotationParameterization {
                                mapping_kind: &metamodel,
                                source_params: vec![None],
                            }),
                        ),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" : C]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("λ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("c")],
                        ),
                        RangeClassTreeNode::Text(". "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[c : C; d : D] b(c,d) : B] λ c,d. b(c,d) : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: vec![Parameterization(
                            &metamodel,
                            vec![
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
                                SectionItem {
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
                                },
                            ],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![
                                            NotationExpression::Param(0, None),
                                            NotationExpression::Param(1, None),
                                        ],
                                    ),
                                ]),
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
                        notation: NotationExpression::Param(
                            0,
                            Some(NotationParameterization {
                                mapping_kind: &metamodel,
                                source_params: vec![None, None],
                            }),
                        ),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" : C; "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" : D]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(","),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("λ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("c")],
                        ),
                        RangeClassTreeNode::Text(","),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("d")],
                        ),
                        RangeClassTreeNode::Text(". "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(","),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[c : C] b(c) : B] a(c ↦ b(c)) : A;",
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
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0, None)],
                                    ),
                                ]),
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
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(
                                    0,
                                    Some(NotationParameterization {
                                        mapping_kind: metamodel
                                            .opposite_mapping
                                            .as_ref()
                                            .unwrap()
                                            .as_ref(),
                                        source_params: vec![None],
                                    }),
                                )],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" : C]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("b"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("c")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[c : C; d : D] b(c,d) : B] a((c,d) ↦ b(c,d)) : A;",
            &metamodel,
            vec![SectionItem {
                parameterizations: vec![Parameterization(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: vec![Parameterization(
                            &metamodel,
                            vec![
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
                                SectionItem {
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
                                },
                            ],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![
                                            NotationExpression::Param(0, None),
                                            NotationExpression::Param(1, None),
                                        ],
                                    ),
                                ]),
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
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(
                                    0,
                                    Some(NotationParameterization {
                                        mapping_kind: metamodel
                                            .opposite_mapping
                                            .as_ref()
                                            .unwrap()
                                            .as_ref(),
                                        source_params: vec![None, None],
                                    }),
                                )],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" : C; "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" : D]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(","),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(","),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("b"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("c")],
                                                ),
                                                RangeClassTreeNode::Text(","),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("d")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
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
                                            vec![NotationExpression::Param(0, None)],
                                        ),
                                    ]),
                                },
                                Parameter {
                                    notation: NotationExpression::Sequence(vec![
                                        NotationExpression::Identifier("c".into()),
                                        NotationExpression::Paren(
                                            '(',
                                            vec![NotationExpression::Param(0, None)],
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
                                vec![
                                    NotationExpression::Param(
                                        0,
                                        Some(NotationParameterization {
                                            mapping_kind: metamodel
                                                .opposite_mapping
                                                .as_ref()
                                                .unwrap()
                                                .as_ref(),
                                            source_params: vec![None],
                                        }),
                                    ),
                                    NotationExpression::Param(
                                        1,
                                        Some(NotationParameterization {
                                            mapping_kind: metamodel
                                                .opposite_mapping
                                                .as_ref()
                                                .unwrap()
                                                .as_ref(),
                                            source_params: vec![None],
                                        }),
                                    ),
                                ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" : D]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(","),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("c"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("b"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("d")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(", "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("c"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("d")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[c : C] b(c) : B] a(c ↦ b(x)) : A;",
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
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0, None)],
                                    ),
                                ]),
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
                            NotationExpression::Paren('(', Vec::new()),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "b(x)".into(),
                severity: Severity::Error,
                msg: "mapping target must match notation of a parameter".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" : C]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" ↦ b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![RangeClassTreeNode::Text("(x)")],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[c : C] b(c) : B] a((c,d) ↦ b(c)) : A;",
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
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0, None)],
                                    ),
                                ]),
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
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(
                                    0,
                                    Some(NotationParameterization {
                                        mapping_kind: metamodel
                                            .opposite_mapping
                                            .as_ref()
                                            .unwrap()
                                            .as_ref(),
                                        source_params: vec![None, None],
                                    }),
                                )],
                            ),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "(c,d) ↦ b(c)".into(),
                severity: Severity::Error,
                msg: "mapping target is parameterized by 1 parameter(s), but mapping source contains 2 parameter(s)".into(),
            }],
                    vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" : C]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(","),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("b"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("c")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[c : C] b(c) : B] a((c,d) ↦ b(d)) : A;",
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
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0, None)],
                                    ),
                                ]),
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
                            NotationExpression::Paren('(', Vec::new()),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "b(d)".into(),
                severity: Severity::Error,
                msg: "mapping target must match notation of a parameter".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" : C]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(","),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" ↦ b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[c : C] b(c) : B] a(d ↦ b(d)) : A;",
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
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0, None)],
                                    ),
                                ]),
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
                            NotationExpression::Paren(
                                '(',
                                vec![NotationExpression::Param(
                                    0,
                                    Some(NotationParameterization {
                                        mapping_kind: metamodel
                                            .opposite_mapping
                                            .as_ref()
                                            .unwrap()
                                            .as_ref(),
                                        source_params: vec![None],
                                    }),
                                )],
                            ),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "d ↦ b(d)".into(),
                severity: Severity::Warning,
                msg: "mapping source notation does not match original parameterization".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" : C]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("b"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("d")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[c : C] b(c) : B] a(c ↦ b(c), d ↦ b(d)) : A;",
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
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("b".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(0, None)],
                                    ),
                                ]),
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
                            NotationExpression::Paren(
                                '(',
                                vec![
                                    NotationExpression::Param(
                                        0,
                                        Some(NotationParameterization {
                                            mapping_kind: metamodel
                                                .opposite_mapping
                                                .as_ref()
                                                .unwrap()
                                                .as_ref(),
                                            source_params: vec![None],
                                        }),
                                    ),
                                    NotationExpression::Param(
                                        0,
                                        Some(NotationParameterization {
                                            mapping_kind: metamodel
                                                .opposite_mapping
                                                .as_ref()
                                                .unwrap()
                                                .as_ref(),
                                            source_params: vec![None],
                                        }),
                                    ),
                                ],
                            ),
                        ]),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":".into(), IdentifierType::Unquoted)),
                        DataToken::Token(Token::Identifier("A".into(), IdentifierType::Unquoted)),
                    ],
                ),
            }],
            &[
                TestDiagnosticMessage {
                    range_text: "d ↦ b(d)".into(),
                    severity: Severity::Warning,
                    msg: "mapping source notation does not match original parameterization".into(),
                },
                TestDiagnosticMessage {
                    range_text: "b(d)".into(),
                    severity: Severity::Error,
                    msg: "parameter referenced multiple times in notation".into(),
                },
            ],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" : C]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("c")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("b"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("c")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(", "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("b"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("d")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[[e : E] d(e) : D] b(e ↦ d(e)),c(λ e. d(e)) : B] \
                              a((e ↦ d(e)) ↦ b(e ↦ d(e)), λ λ e. d(e). c(λ e. d(e))) : A;",
            &metamodel,
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
                                                notation: NotationExpression::Identifier(
                                                    "e".into(),
                                                ),
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
                                    }],
                                )],
                                body: SectionItemBody::ParamGroup(
                                    vec![Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("d".into()),
                                            NotationExpression::Paren(
                                                '(',
                                                vec![NotationExpression::Param(0, None)],
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
                            }],
                        )],
                        body: SectionItemBody::ParamGroup(
                            vec![
                                Parameter {
                                    notation: NotationExpression::Sequence(vec![
                                        NotationExpression::Identifier("b".into()),
                                        NotationExpression::Paren(
                                            '(',
                                            vec![NotationExpression::Param(
                                                0,
                                                Some(NotationParameterization {
                                                    mapping_kind: metamodel
                                                        .opposite_mapping
                                                        .as_ref()
                                                        .unwrap()
                                                        .as_ref(),
                                                    source_params: vec![None],
                                                }),
                                            )],
                                        ),
                                    ]),
                                },
                                Parameter {
                                    notation: NotationExpression::Sequence(vec![
                                        NotationExpression::Identifier("c".into()),
                                        NotationExpression::Paren(
                                            '(',
                                            vec![NotationExpression::Param(
                                                0,
                                                Some(NotationParameterization {
                                                    mapping_kind: &metamodel,
                                                    source_params: vec![None],
                                                }),
                                            )],
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
                                vec![
                                    NotationExpression::Param(
                                        0,
                                        Some(NotationParameterization {
                                            mapping_kind: metamodel
                                                .opposite_mapping
                                                .as_ref()
                                                .unwrap()
                                                .as_ref(),
                                            source_params: vec![Some(NotationParameterization {
                                                mapping_kind: metamodel
                                                    .opposite_mapping
                                                    .as_ref()
                                                    .unwrap()
                                                    .as_ref(),
                                                source_params: vec![None],
                                            })],
                                        }),
                                    ),
                                    NotationExpression::Param(
                                        1,
                                        Some(NotationParameterization {
                                            mapping_kind: &metamodel,
                                            source_params: vec![Some(NotationParameterization {
                                                mapping_kind: &metamodel,
                                                source_params: vec![None],
                                            })],
                                        }),
                                    ),
                                ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("["),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("e")],
                                        ),
                                        RangeClassTreeNode::Text(" : E]"),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("d"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("e")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" : D]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("b"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("e")],
                                        ),
                                        RangeClassTreeNode::Text(" ↦ "),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![
                                                RangeClassTreeNode::Text("d"),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::Paren,
                                                    vec![
                                                        RangeClassTreeNode::Text("("),
                                                        RangeClassTreeNode::Range(
                                                            RangeClass::ParamRef(
                                                                ParamScopeClass::Local,
                                                            ),
                                                            vec![RangeClassTreeNode::Text("e")],
                                                        ),
                                                        RangeClassTreeNode::Text(")"),
                                                    ],
                                                ),
                                            ],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(","),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("c"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("(λ "),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("e")],
                                        ),
                                        RangeClassTreeNode::Text(". "),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![
                                                RangeClassTreeNode::Text("d"),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::Paren,
                                                    vec![
                                                        RangeClassTreeNode::Text("("),
                                                        RangeClassTreeNode::Range(
                                                            RangeClass::ParamRef(
                                                                ParamScopeClass::Local,
                                                            ),
                                                            vec![RangeClassTreeNode::Text("e")],
                                                        ),
                                                        RangeClassTreeNode::Text(")"),
                                                    ],
                                                ),
                                            ],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : B]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![
                        RangeClassTreeNode::Text("a"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamNotation(
                                                        ParamScopeClass::Local,
                                                    ),
                                                    vec![RangeClassTreeNode::Text("e")],
                                                ),
                                                RangeClassTreeNode::Text(" ↦ d"),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::Paren,
                                                    vec![
                                                        RangeClassTreeNode::Text("("),
                                                        RangeClassTreeNode::Range(
                                                            RangeClass::ParamRef(
                                                                ParamScopeClass::Local,
                                                            ),
                                                            vec![RangeClassTreeNode::Text("e")],
                                                        ),
                                                        RangeClassTreeNode::Text(")"),
                                                    ],
                                                ),
                                            ],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("b"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![
                                                        RangeClassTreeNode::Range(
                                                            RangeClass::ParamNotation(
                                                                ParamScopeClass::Local,
                                                            ),
                                                            vec![RangeClassTreeNode::Text("e")],
                                                        ),
                                                        RangeClassTreeNode::Text(" ↦ d"),
                                                        RangeClassTreeNode::Range(
                                                            RangeClass::Paren,
                                                            vec![
                                                                RangeClassTreeNode::Text("("),
                                                                RangeClassTreeNode::Range(
                                                                    RangeClass::ParamRef(
                                                                        ParamScopeClass::Local,
                                                                    ),
                                                                    vec![RangeClassTreeNode::Text(
                                                                        "e",
                                                                    )],
                                                                ),
                                                                RangeClassTreeNode::Text(")"),
                                                            ],
                                                        ),
                                                    ],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(", λ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("λ "),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("e")],
                                        ),
                                        RangeClassTreeNode::Text(". d"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("e")],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(". "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("c"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("("),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![
                                                        RangeClassTreeNode::Text("λ "),
                                                        RangeClassTreeNode::Range(
                                                            RangeClass::ParamNotation(
                                                                ParamScopeClass::Local,
                                                            ),
                                                            vec![RangeClassTreeNode::Text("e")],
                                                        ),
                                                        RangeClassTreeNode::Text(". d"),
                                                        RangeClassTreeNode::Range(
                                                            RangeClass::Paren,
                                                            vec![
                                                                RangeClassTreeNode::Text("("),
                                                                RangeClassTreeNode::Range(
                                                                    RangeClass::ParamRef(
                                                                        ParamScopeClass::Local,
                                                                    ),
                                                                    vec![RangeClassTreeNode::Text(
                                                                        "e",
                                                                    )],
                                                                ),
                                                                RangeClassTreeNode::Text(")"),
                                                            ],
                                                        ),
                                                    ],
                                                ),
                                                RangeClassTreeNode::Text(")"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : A;"),
            ],
        )?;
        Ok(())
    }

    #[test]
    fn sections() -> Result<(), Message> {
        let metamodel = TestMetaModel::new();
        test_parameter_identification(
            "%slate \"test\"; {}",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::Section(&metamodel, Vec::new()),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(RangeClass::Paren, vec![RangeClassTreeNode::Text("{}")]),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; {};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::Section(&metamodel, Vec::new()),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(RangeClass::Paren, vec![RangeClassTreeNode::Text("{}")]),
                RangeClassTreeNode::Text(";"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Global),
                            vec![RangeClassTreeNode::Text("x")],
                        ),
                        RangeClassTreeNode::Text(" : T }"),
                    ],
                ),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Global),
                            vec![RangeClassTreeNode::Text("x")],
                        ),
                        RangeClassTreeNode::Text(" : T; }"),
                    ],
                ),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Global),
                            vec![RangeClassTreeNode::Text("x")],
                        ),
                        RangeClassTreeNode::Text(" : T; "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Global),
                            vec![RangeClassTreeNode::Text("y")],
                        ),
                        RangeClassTreeNode::Text(" : U; }"),
                    ],
                ),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [a,b] { x_a; [c] y_a_b_c; } z_a;",
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
                                            NotationExpression::Param(0, None),
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
                                            NotationExpression::Param(0, None),
                                            NotationExpression::ReservedChar('_'),
                                            NotationExpression::Param(1, None),
                                            NotationExpression::ReservedChar('_'),
                                            NotationExpression::Param(2, None),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text(","),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text("]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Global),
                            vec![
                                RangeClassTreeNode::Text("x_"),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text("; "),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                                RangeClassTreeNode::Text("]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Global),
                            vec![
                                RangeClassTreeNode::Text("y_"),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text("_"),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text("_"),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("c")],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text("; }"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("z_a")],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; [[a] { b_a; }] { c(a ↦ b_a); }",
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
                                        notation: NotationExpression::Identifier("a".into()),
                                    }],
                                    Vec::new(),
                                ),
                            }],
                        )],
                        body: SectionItemBody::Section(
                            &metamodel,
                            vec![SectionItem {
                                parameterizations: Vec::new(),
                                body: SectionItemBody::ParamGroup(
                                    vec![Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("b".into()),
                                            NotationExpression::ReservedChar('_'),
                                            NotationExpression::Param(0, None),
                                        ]),
                                    }],
                                    Vec::new(),
                                ),
                            }],
                        ),
                    }],
                )],
                body: SectionItemBody::Section(
                    &metamodel,
                    vec![SectionItem {
                        parameterizations: Vec::new(),
                        body: SectionItemBody::ParamGroup(
                            vec![Parameter {
                                notation: NotationExpression::Sequence(vec![
                                    NotationExpression::Identifier("c".into()),
                                    NotationExpression::Paren(
                                        '(',
                                        vec![NotationExpression::Param(
                                            0,
                                            Some(NotationParameterization {
                                                mapping_kind: metamodel
                                                    .opposite_mapping
                                                    .as_ref()
                                                    .unwrap()
                                                    .as_ref(),
                                                source_params: vec![None],
                                            }),
                                        )],
                                    ),
                                ]),
                            }],
                            Vec::new(),
                        ),
                    }],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text("]"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" "),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("{ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("b_"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("a")],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text("; }"),
                            ],
                        ),
                        RangeClassTreeNode::Text("]"),
                    ],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Global),
                            vec![
                                RangeClassTreeNode::Text("c"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("a")],
                                        ),
                                        RangeClassTreeNode::Text(" ↦ "),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![
                                                RangeClassTreeNode::Text("b_"),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("a")],
                                                ),
                                            ],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text("; }"),
                    ],
                ),
            ],
        )?;
        Ok(())
    }

    #[test]
    fn objects() -> Result<(), Message> {
        let metamodel = TestMetaModel::new();
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("T")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(RangeClass::Paren, vec![RangeClassTreeNode::Text("{}")]),
                RangeClassTreeNode::Text(";"),
            ],
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
                                extra_sections: Vec::new(),
                            }],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("T")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("x")],
                        ),
                        RangeClassTreeNode::Text("}"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                    extra_sections: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("y".into()),
                                    },
                                    param_data: Vec::new(),
                                    extra_sections: Vec::new(),
                                },
                            ],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("T")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("x")],
                        ),
                        RangeClassTreeNode::Text(" || "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("y")],
                        ),
                        RangeClassTreeNode::Text("}"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                    extra_sections: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("y".into()),
                                    },
                                    param_data: Vec::new(),
                                    extra_sections: Vec::new(),
                                },
                            ],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("T")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("x")],
                        ),
                        RangeClassTreeNode::Text(" | | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("y")],
                        ),
                        RangeClassTreeNode::Text("}"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                    extra_sections: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("y".into()),
                                    },
                                    param_data: Vec::new(),
                                    extra_sections: Vec::new(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("T")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("x")],
                        ),
                        RangeClassTreeNode::Text(" ||| "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("y")],
                        ),
                        RangeClassTreeNode::Text("}"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                            vec![NotationExpression::Param(0, None)],
                                        ),
                                    ]),
                                },
                                param_data: Vec::new(),
                                extra_sections: vec![vec![SectionItem {
                                    parameterizations: Vec::new(),
                                    body: SectionItemBody::ParamGroup(
                                        vec![Parameter {
                                            notation: NotationExpression::Identifier("z".into()),
                                        }],
                                        Vec::new(),
                                    ),
                                }]],
                            }],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("T")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![
                                RangeClassTreeNode::Text("x"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("y")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("y")],
                        ),
                        RangeClassTreeNode::Text(" | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Extra),
                            vec![RangeClassTreeNode::Text("z")],
                        ),
                        RangeClassTreeNode::Text("}"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                                vec![NotationExpression::Param(0, None)],
                                            ),
                                        ]),
                                    },
                                    param_data: Vec::new(),
                                    extra_sections: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: Vec::new(),
                                    param: Parameter {
                                        notation: NotationExpression::Identifier("z".into()),
                                    },
                                    param_data: Vec::new(),
                                    extra_sections: Vec::new(),
                                },
                            ],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("T")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![
                                RangeClassTreeNode::Text("x"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("y")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("y")],
                        ),
                        RangeClassTreeNode::Text(" || "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("z")],
                        ),
                        RangeClassTreeNode::Text("}"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; T := {x(y) | y | z := λ a};",
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
                                            vec![NotationExpression::Param(0, None)],
                                        ),
                                    ]),
                                },
                                param_data: Vec::new(),
                                extra_sections: vec![vec![SectionItem {
                                    parameterizations: Vec::new(),
                                    body: SectionItemBody::ParamGroup(
                                        vec![Parameter {
                                            notation: NotationExpression::Identifier("z".into()),
                                        }],
                                        vec![
                                            DataToken::Token(Token::Identifier(
                                                ":=".into(),
                                                IdentifierType::Unquoted,
                                            )),
                                            DataToken::Mapping(
                                                &metamodel,
                                                vec![MappingParameter(
                                                    None,
                                                    Parameter {
                                                        notation: NotationExpression::Identifier(
                                                            "a".into(),
                                                        ),
                                                    },
                                                    Vec::new(),
                                                )],
                                                Vec::new(),
                                            ),
                                        ],
                                    ),
                                }]],
                            }],
                        ),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "'.' expected".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("T")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![
                                RangeClassTreeNode::Text("x"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("y")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("y")],
                        ),
                        RangeClassTreeNode::Text(" | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Extra),
                            vec![RangeClassTreeNode::Text("z")],
                        ),
                        RangeClassTreeNode::Text(" := λ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text("}"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; c := {x_i ↦ i | i : I || y_j_k ↦ j k | j : J; k : K | a | b} | {z};",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("c".into()),
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
                                            NotationExpression::Param(0, None),
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
                                    extra_sections: Vec::new(),
                                },
                                ObjectItem {
                                    parameterizations: vec![Parameterization(
                                        &metamodel,
                                        vec![
                                            SectionItem {
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
                                            },
                                            SectionItem {
                                                parameterizations: Vec::new(),
                                                body: SectionItemBody::ParamGroup(
                                                    vec![Parameter {
                                                        notation: NotationExpression::Identifier(
                                                            "k".into(),
                                                        ),
                                                    }],
                                                    vec![
                                                        DataToken::Token(Token::Identifier(
                                                            ":".into(),
                                                            IdentifierType::Unquoted,
                                                        )),
                                                        DataToken::Token(Token::Identifier(
                                                            "K".into(),
                                                            IdentifierType::Unquoted,
                                                        )),
                                                    ],
                                                ),
                                            },
                                        ],
                                    )],
                                    param: Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("y".into()),
                                            NotationExpression::ReservedChar('_'),
                                            NotationExpression::Param(0, None),
                                            NotationExpression::ReservedChar('_'),
                                            NotationExpression::Param(1, None),
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
                                        DataToken::Token(Token::Identifier(
                                            "k".into(),
                                            IdentifierType::Unquoted,
                                        )),
                                    ],
                                    extra_sections: vec![
                                        vec![SectionItem {
                                            parameterizations: Vec::new(),
                                            body: SectionItemBody::ParamGroup(
                                                vec![Parameter {
                                                    notation: NotationExpression::Identifier(
                                                        "a".into(),
                                                    ),
                                                }],
                                                Vec::new(),
                                            ),
                                        }],
                                        vec![SectionItem {
                                            parameterizations: Vec::new(),
                                            body: SectionItemBody::ParamGroup(
                                                vec![Parameter {
                                                    notation: NotationExpression::Identifier(
                                                        "b".into(),
                                                    ),
                                                }],
                                                Vec::new(),
                                            ),
                                        }],
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
                                extra_sections: Vec::new(),
                            }],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("c")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Object),
                            vec![
                                RangeClassTreeNode::Text("x_"),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("i")],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ i | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("i")],
                        ),
                        RangeClassTreeNode::Text(" : I || "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Object),
                            vec![
                                RangeClassTreeNode::Text("y_"),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("j")],
                                ),
                                RangeClassTreeNode::Text("_"),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("k")],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ j k | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("j")],
                        ),
                        RangeClassTreeNode::Text(" : J; "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("k")],
                        ),
                        RangeClassTreeNode::Text(" : K | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Extra),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text(" | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Extra),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text("}"),
                    ],
                ),
                RangeClassTreeNode::Text(" | "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("z")],
                        ),
                        RangeClassTreeNode::Text("}"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                    extra_sections: Vec::new(),
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
                                                vec![NotationExpression::Param(0, None)],
                                            ),
                                        ]),
                                    },
                                    param_data: Vec::new(),
                                    extra_sections: Vec::new(),
                                },
                            ],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("ℕ")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("{"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![RangeClassTreeNode::Text("@\"0\"")],
                        ),
                        RangeClassTreeNode::Text(" || "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Object),
                            vec![
                                RangeClassTreeNode::Text("S"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("n")],
                                        ),
                                        RangeClassTreeNode::Text(")"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" | "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("n")],
                        ),
                        RangeClassTreeNode::Text(" : ℕ}"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        Ok(())
    }

    #[test]
    fn prefix_mappings() -> Result<(), Message> {
        let metamodel = TestMetaModel::new();
        test_parameter_identification(
            "%slate \"test\"; f := λ. x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Mapping(
                            &metamodel,
                            Vec::new(),
                            vec![DataToken::Token(Token::Identifier(
                                "x".into(),
                                IdentifierType::Unquoted,
                            ))],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ. x;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := λ a. x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
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
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(". x;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := λ a : A. x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Mapping(
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
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" : A. x;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := (λ a. x, λ b. y);",
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("(λ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text(". x, λ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(". y)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := λ a,b. x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Mapping(
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
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(","),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("b")],
                ),
                RangeClassTreeNode::Text(". x;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := λ a,b,. x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Mapping(
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
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(","),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("b")],
                ),
                RangeClassTreeNode::Text(",. x;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := λ a,,b. x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Mapping(
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
                        ),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: ",".into(),
                severity: Severity::Error,
                msg: "superfluous comma".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(",,"),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("b")],
                ),
                RangeClassTreeNode::Text(". x;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := λ a : A, b : B. x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Mapping(
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
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" : A, "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("b")],
                ),
                RangeClassTreeNode::Text(" : B. x;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := λ a;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Mapping(
                            &metamodel,
                            vec![MappingParameter(
                                None,
                                Parameter {
                                    notation: NotationExpression::Identifier("a".into()),
                                },
                                Vec::new(),
                            )],
                            Vec::new(),
                        ),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "'.' expected".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := (λ a);",
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
                                Vec::new(),
                            )],
                        ),
                    ],
                ),
            }],
            &[TestDiagnosticMessage {
                range_text: "".into(),
                severity: Severity::Error,
                msg: "'.' expected".into(),
            }],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("(λ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text(")"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := λ a : A, λ b : B. c_b : C, d : D. x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Mapping(
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
                                            NotationExpression::Param(0, None),
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
                                MappingParameter(
                                    None,
                                    Parameter {
                                        notation: NotationExpression::Identifier("d".into()),
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
                            ],
                            vec![DataToken::Token(Token::Identifier(
                                "x".into(),
                                IdentifierType::Unquoted,
                            ))],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" : A, λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("b")],
                ),
                RangeClassTreeNode::Text(" : B. "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![
                        RangeClassTreeNode::Text("c_"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : C, "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("d")],
                ),
                RangeClassTreeNode::Text(" : D. x;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := λ a : A, b : B ↦ c_b : C, d : D. x;",
            &metamodel,
            vec![SectionItem {
                parameterizations: Vec::new(),
                body: SectionItemBody::ParamGroup(
                    vec![Parameter {
                        notation: NotationExpression::Identifier("f".into()),
                    }],
                    vec![
                        DataToken::Token(Token::Identifier(":=".into(), IdentifierType::Unquoted)),
                        DataToken::Mapping(
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
                                        metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
                                            NotationExpression::Param(0, None),
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
                                MappingParameter(
                                    None,
                                    Parameter {
                                        notation: NotationExpression::Identifier("d".into()),
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
                            ],
                            vec![DataToken::Token(Token::Identifier(
                                "x".into(),
                                IdentifierType::Unquoted,
                            ))],
                        ),
                    ],
                ),
            }],
            &[],
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := λ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" : A, "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("b")],
                ),
                RangeClassTreeNode::Text(" : B ↦ "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![
                        RangeClassTreeNode::Text("c_"),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamRef(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                    ],
                ),
                RangeClassTreeNode::Text(" : C, "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Local),
                    vec![RangeClassTreeNode::Text("d")],
                ),
                RangeClassTreeNode::Text(" : D. x;"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; a := f[λ b : B. b, λ λ d : D, e : E, f : E. c[d,f] : C. c[0,1]];",
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
                                                        NotationExpression::Param(0, None),
                                                        NotationExpression::Param(2, None),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" := f"),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("[λ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(" : B. b, λ λ "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("d")],
                        ),
                        RangeClassTreeNode::Text(" : D, "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("e")],
                        ),
                        RangeClassTreeNode::Text(" : E, "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("f")],
                        ),
                        RangeClassTreeNode::Text(" : E. "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("c"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("["),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(","),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("f")],
                                        ),
                                        RangeClassTreeNode::Text("]"),
                                    ],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" : C. c"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::Number,
                                    vec![RangeClassTreeNode::Text("0")],
                                ),
                                RangeClassTreeNode::Text(","),
                                RangeClassTreeNode::Range(
                                    RangeClass::Number,
                                    vec![RangeClassTreeNode::Text("1")],
                                ),
                                RangeClassTreeNode::Text("]"),
                            ],
                        ),
                        RangeClassTreeNode::Text("]"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        Ok(())
    }

    #[test]
    fn infix_mappings() -> Result<(), Message> {
        let metamodel = TestMetaModel::new();
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![RangeClassTreeNode::Text("()")],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text(" : A ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text(" : A)"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := (a(b) ↦ x);",
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
                                vec![MappingParameter(
                                    None,
                                    Parameter {
                                        notation: NotationExpression::Sequence(vec![
                                            NotationExpression::Identifier("a".into()),
                                            NotationExpression::Paren(
                                                '(',
                                                vec![NotationExpression::Identifier("b".into())],
                                            ),
                                        ]),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![
                                RangeClassTreeNode::Text("a"),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![RangeClassTreeNode::Text("(b)")],
                                ),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                    metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("(a, "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                    metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
                                    metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("a")],
                        ),
                        RangeClassTreeNode::Text(" ↦ x, "),
                        RangeClassTreeNode::Range(
                            RangeClass::ParamNotation(ParamScopeClass::Local),
                            vec![RangeClassTreeNode::Text("b")],
                        ),
                        RangeClassTreeNode::Text(" ↦ y)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text(","),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text(","),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text(",)"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text(",,"),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text(")"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text(" : A, "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text(" : B)"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := ((a : A, b : B ↦ c_b : C, d : D) ↦ x);",
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
                                            metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
                                                NotationExpression::Param(0, None),
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
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("d".into()),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text(" : A, "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text(" : B ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("c_"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("b")],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" : C, "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" : D)"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification(
            "%slate \"test\"; f := ((a : A, λ b : B. c_b : C, d : D) ↦ x);",
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
                                metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
                                            metamodel
                                                .opposite_mapping
                                                .as_ref()
                                                .unwrap()
                                                .opposite_mapping
                                                .as_ref()
                                                .unwrap()
                                                .as_ref(),
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
                                                NotationExpression::Param(0, None),
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
                                    MappingParameter(
                                        None,
                                        Parameter {
                                            notation: NotationExpression::Identifier("d".into()),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("f")],
                ),
                RangeClassTreeNode::Text(" := "),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("("),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("a")],
                                ),
                                RangeClassTreeNode::Text(" : A, λ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text(" : B. "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("c_"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamRef(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("b")],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" : C, "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("d")],
                                ),
                                RangeClassTreeNode::Text(" : D)"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ x)"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
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
                                    metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
                                    metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
                                    vec![MappingParameter(
                                        Some(MappingParameterization(
                                            metamodel.opposite_mapping.as_ref().unwrap().as_ref(),
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
                                                        NotationExpression::Param(0, None),
                                                        NotationExpression::Param(2, None),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("a")],
                ),
                RangeClassTreeNode::Text(" := f"),
                RangeClassTreeNode::Range(
                    RangeClass::Paren,
                    vec![
                        RangeClassTreeNode::Text("["),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![RangeClassTreeNode::Text("b")],
                                ),
                                RangeClassTreeNode::Text(" : B)"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ b, "),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("("),
                                RangeClassTreeNode::Range(
                                    RangeClass::Paren,
                                    vec![
                                        RangeClassTreeNode::Text("("),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("d")],
                                        ),
                                        RangeClassTreeNode::Text(" : D, "),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("e")],
                                        ),
                                        RangeClassTreeNode::Text(" : E, "),
                                        RangeClassTreeNode::Range(
                                            RangeClass::ParamNotation(ParamScopeClass::Local),
                                            vec![RangeClassTreeNode::Text("f")],
                                        ),
                                        RangeClassTreeNode::Text(" : E)"),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" ↦ "),
                                RangeClassTreeNode::Range(
                                    RangeClass::ParamNotation(ParamScopeClass::Local),
                                    vec![
                                        RangeClassTreeNode::Text("c"),
                                        RangeClassTreeNode::Range(
                                            RangeClass::Paren,
                                            vec![
                                                RangeClassTreeNode::Text("["),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("d")],
                                                ),
                                                RangeClassTreeNode::Text(","),
                                                RangeClassTreeNode::Range(
                                                    RangeClass::ParamRef(ParamScopeClass::Local),
                                                    vec![RangeClassTreeNode::Text("f")],
                                                ),
                                                RangeClassTreeNode::Text("]"),
                                            ],
                                        ),
                                    ],
                                ),
                                RangeClassTreeNode::Text(" : C)"),
                            ],
                        ),
                        RangeClassTreeNode::Text(" ↦ c"),
                        RangeClassTreeNode::Range(
                            RangeClass::Paren,
                            vec![
                                RangeClassTreeNode::Text("["),
                                RangeClassTreeNode::Range(
                                    RangeClass::Number,
                                    vec![RangeClassTreeNode::Text("0")],
                                ),
                                RangeClassTreeNode::Text(","),
                                RangeClassTreeNode::Range(
                                    RangeClass::Number,
                                    vec![RangeClassTreeNode::Text("1")],
                                ),
                                RangeClassTreeNode::Text("]"),
                            ],
                        ),
                        RangeClassTreeNode::Text("]"),
                    ],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        Ok(())
    }

    #[test]
    fn top_level_errors() -> Result<(), Message> {
        let metamodel = TestMetaModel::new();
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
            Vec::new(),
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"unknown\"")],
                ),
                RangeClassTreeNode::Text(";"),
            ],
        )?;
        test_parameter_identification_with_document(
            "%slate \"unknown\"; x;",
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"unknown\"")],
                ),
                RangeClassTreeNode::Text("; x;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text(" x"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text(";; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(
                    RangeClass::ParamNotation(ParamScopeClass::Global),
                    vec![RangeClassTreeNode::Text("x")],
                ),
                RangeClassTreeNode::Text(" : T;;"),
            ],
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
            vec![
                RangeClassTreeNode::Range(
                    RangeClass::Keyword,
                    vec![RangeClassTreeNode::Text("%slate")],
                ),
                RangeClassTreeNode::Text(" "),
                RangeClassTreeNode::Range(
                    RangeClass::String,
                    vec![RangeClassTreeNode::Text("\"test\"")],
                ),
                RangeClassTreeNode::Text("; "),
                RangeClassTreeNode::Range(RangeClass::Paren, vec![RangeClassTreeNode::Text("{}")]),
                RangeClassTreeNode::Text(";;"),
            ],
        )?;
        Ok(())
    }

    struct Document<'a> {
        metamodel: Option<&'a dyn MetaModel>,
        definitions: Section<'a>,
    }

    impl<'a> IntoEvents<ParameterEvent<'a>> for Document<'a> {
        fn fill_events(self, result: &mut Vec<ParameterEvent<'a>>) {
            if let Some(metamodel) = self.metamodel {
                result.push(ParameterEvent::MetaModel(metamodel));
            }
            self.definitions.fill_events(result);
        }
    }

    type Section<'a> = Vec<SectionItem<'a>>;

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

    struct Parameterization<'a>(&'a dyn SectionKind, Section<'a>);

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
        Section(&'a dyn SectionKind, Section<'a>),
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
        Mapping(
            &'a dyn MappingKind<dyn DataKind>,
            Vec<MappingParameter<'a>>,
            Data<'a>,
        ),
        Object(&'a dyn ObjectKind, Object<'a>),
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
            if let Some(parameterization) = self.0 {
                Self::group(
                    Some(parameterization.0),
                    result,
                    |event| ParameterEvent::MappingParam(event),
                    |result| {
                        parameterization.1.fill_events(result);
                        self.1.fill_events(result);
                        self.2.fill_events(result);
                    },
                );
            } else {
                Self::group(
                    None,
                    result,
                    |event| ParameterEvent::MappingParam(event),
                    |result| {
                        self.1.fill_events(result);
                        self.2.fill_events(result);
                    },
                );
            }
        }
    }

    struct MappingParameterization<'a>(
        &'a dyn MappingKind<dyn ParamKind>,
        Vec<MappingParameter<'a>>,
    );

    type Object<'a> = Vec<ObjectItem<'a>>;

    struct ObjectItem<'a> {
        parameterizations: Vec<Parameterization<'a>>,
        param: Parameter<'a>,
        param_data: Data<'a>,
        extra_sections: Vec<Section<'a>>,
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
                    for section in self.extra_sections {
                        Self::group(
                            (),
                            result,
                            |event| ParameterEvent::ObjectItemExtra(event),
                            |result| section.fill_events(result),
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
        expected_ranges: RangeClassTree,
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
            expected_ranges,
        )
    }

    fn test_parameter_identification_with_document(
        input: &str,
        metamodel: &TestMetaModel,
        expected_document: Document,
        expected_diagnostics: &[TestDiagnosticMessage],
        expected_ranges: RangeClassTree,
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
        let (diagnostics, range_events) = diag_sink.results();
        assert_eq!(diagnostics, expected_diagnostics);
        assert_eq!((range_events, input.len()), expected_ranges.into_events());
        Ok(())
    }
}
