use std::{borrow::Cow, fmt::Debug, mem::take, ops::Range, slice};

use either::Either;
use lang_def::{
    mem_serializable::*,
    parser::{buffer::BufferedParserInterface, compose::*, *},
};
use temp_inst::{TempRef, TempRepr};
use temp_stack::TempStack;

use super::{layer1_tokenizer::*, layer2_parenthesis_matcher::*, metamodel::*};

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub enum ParameterEvent<'a, Pos: Position> {
    SectionStart(Parameterized<'a, Pos, &'static dyn SectionKind>),
    SectionEnd,
    ParamGroup(Parameterized<'a, Pos, ParamGroup<'a, Pos>>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Parameterized<'a, Pos: Position, T> {
    pub parameterizations: Vec<WithSpan<Parameterization<'a, Pos>, Pos>>,
    pub prefixes: Vec<WithSpan<NotationExpr<'a>, Pos>>,
    pub data: Option<T>, // `None` in case of some parse errors
}

impl<'a, Pos: Position, T: MemSerializable<Pos>> MemSerializable<Pos>
    for Parameterized<'a, Pos, T>
{
    type Serialized = (
        <Vec<WithSpan<Parameterization<'a, Pos>, Pos>> as MemSerializable<Pos>>::Serialized,
        <Vec<WithSpan<NotationExpr<'a>, Pos>> as MemSerializable<Pos>>::Serialized,
        <Option<T> as MemSerializable<Pos>>::Serialized,
    );

    fn serialize(&self, relative_to: &Pos) -> Self::Serialized {
        (
            self.parameterizations.serialize(relative_to),
            self.prefixes.serialize(relative_to),
            self.data.serialize(relative_to),
        )
    }

    fn deserialize(serialized: &Self::Serialized, relative_to: &Pos) -> Self {
        Parameterized {
            parameterizations: <_>::deserialize(&serialized.0, relative_to),
            prefixes: <_>::deserialize(&serialized.1, relative_to),
            data: <_>::deserialize(&serialized.2, relative_to),
        }
    }
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Parameterization<'a, Pos: Position> {
    pub kind: &'static dyn SectionKind,
    pub items: SectionItems<'a, Pos>,
}

pub type SectionItems<'a, Pos> = Vec<Parameterized<'a, Pos, SectionItem<'a, Pos>>>;

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub enum SectionItem<'a, Pos: Position> {
    Section(Section<'a, Pos>),
    ParamGroup(ParamGroup<'a, Pos>),
}

// TODO: handle prefixes within parameterizations correctly

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Section<'a, Pos: Position> {
    pub kind: &'static dyn SectionKind,
    pub items: SectionItems<'a, Pos>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Param<'a, Pos: Position> {
    pub notation: Option<WithSpan<Notation<'a>, Pos>>,
    pub data: Tokens<'a, Pos>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct ParamGroup<'a, Pos: Position> {
    pub param_notations: Vec<WithSpan<Notation<'a>, Pos>>,
    pub data: Tokens<'a, Pos>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub enum TokenTree<'a, Pos: Position> {
    Token(Token<'a>),
    Paren(char, Tokens<'a, Pos>),
    Parameterization(Parameterization<'a, Pos>),
    Mapping(Mapping<'a, Pos>),
    Object(Object<'a, Pos>),
}

pub type Tokens<'a, Pos> = Vec<WithSpan<TokenTree<'a, Pos>, Pos>>;

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Mapping<'a, Pos: Position> {
    pub kind: &'static dyn MappingKind,
    pub params: Vec<MappingParam<'a, Pos>>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct MappingParam<'a, Pos: Position> {
    pub mappings: Vec<Mapping<'a, Pos>>,
    pub notation: Option<WithSpan<Notation<'a>, Pos>>,
    pub data: Tokens<'a, Pos>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Object<'a, Pos: Position> {
    pub kind: &'static dyn ObjectKind,
    pub items: Vec<ObjectItem<'a, Pos>>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct ObjectItem<'a, Pos: Position> {
    pub parameterization: Parameterization<'a, Pos>,
    pub param: Param<'a, Pos>,
    pub extra_parts: Vec<SectionItems<'a, Pos>>,
}

// Note: It is important that notation expressions do not depend on positions, as they are a
// potentially long-lived part of the parameter identifier state, so position information would
// cause frequent re-parsing.
#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Notation<'a> {
    pub expr: NotationExpr<'a>,
    pub scope: NameScopeDesc,
    pub kind: Option<NameKindDesc>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub enum NotationExpr<'a> {
    ReservedChar(char),
    Ident(Cow<'a, str>),
    Seq(Vec<NotationExpr<'a>>),
    Paren(char, Vec<Vec<NotationExpr<'a>>>),
    Mapping(Box<MappingNotationExpr<'a>>),
    Param(ParamIdx),
}

impl<'a> NotationExpr<'a> {
    pub fn find_in_sequence(&self, seq: &[Self]) -> Option<Range<usize>> {
        if let NotationExpr::Seq(exprs) = self {
            // Could be simplified once `Iterator::map_windows` is stabilized.
            let seq_len = seq.len();
            let exprs_len = exprs.len();
            if seq_len >= exprs_len {
                for idx in 0..=(seq_len - exprs_len) {
                    let range = idx..(idx + exprs_len);
                    let sub_seq = &seq[range.clone()];
                    if sub_seq == exprs {
                        return Some(range);
                    }
                }
            }
        } else {
            if let Some(idx) = seq.iter().position(|item| item == self) {
                return Some(idx..(idx + 1));
            }
        }
        None
    }

    fn contains_param_ref(&self, range: Range<ParamIdx>) -> bool {
        match self {
            NotationExpr::ReservedChar(_) | NotationExpr::Ident(_) => false,
            NotationExpr::Seq(items) => items
                .iter()
                .any(|item| item.contains_param_ref(range.clone())),
            NotationExpr::Paren(_, rows) => rows.iter().any(|cols| {
                cols.iter()
                    .any(|item| item.contains_param_ref(range.clone()))
            }),
            NotationExpr::Mapping(mapping) => mapping.target_expr.contains_param_ref(
                (range.start - mapping.params_len as isize)
                    ..(range.end - mapping.params_len as isize),
            ),
            NotationExpr::Param(idx) => range.contains(idx),
        }
    }
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct MappingNotationExpr<'a> {
    pub kind: &'static dyn MappingKind,
    pub params_len: usize,
    pub target_expr: NotationExpr<'a>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
struct NotationInfo<'a> {
    parameterizations_rev: Vec<NotationExpr<'a>>,
    notation: Notation<'a>,
}

// In notation expressions, only negative values are used, which are negated 1-based De Bruijn
// indices.
// In later layers, nonnegative values are De Bruijn levels indexing into the flattened list of
// globals.
pub type ParamIdx = isize;

// Nonnegative values are De Bruijn levels, indexing into the flattened list of section items.
// Negative values are De Bruijn indices, indexing into the ctx consisting of parameterizations
// and mappings.
pub type ParamRef = isize;

#[derive(MemSerializable)]
pub struct ParameterIdentifier<'a> {
    open_sections: Vec<OpenSection<'a>>,
}

impl<'a> ParameterIdentifier<'a> {
    pub fn new() -> Self {
        ParameterIdentifier {
            open_sections: Vec::new(),
        }
    }
}

impl<
        'a,
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    > Parser<IF> for ParameterIdentifier<'a>
{
    fn parse(&mut self, interface: &mut IF) -> bool {
        let (_, config) = interface.config();
        let Some(metamodel) = config.metamodel else {
            return Self::parse_metamodel(interface);
        };

        let section_kind = self
            .open_sections
            .last()
            .map(|open_section| open_section.kind)
            .unwrap_or_else(|| metamodel.top_level_section_kind());

        {
            let Some(token) = interface.input().look_ahead() else {
                return true;
            };
            if let TokenEvent::ParenEnd = *token {
                let token = token.consume();
                interface.out(&token, ParameterEvent::SectionEnd);
                self.open_sections.pop();
                let Some(next_token) = interface.input().look_ahead() else {
                    return true;
                };
                if let TokenEvent::Token(Token::ReservedChar(';', _, _)) = *next_token {
                    let next_token = next_token.consume();
                    interface.warning(
                        &next_token,
                        Some(WarningKind::SyntaxWarning),
                        format!("superfluous semicolon"),
                    );
                }
                return false;
            }
        }

        let parameterizations = Self::parse_parameterizations(interface, section_kind);

        let mut param_notations_rev = Vec::new();
        for parameterization in &parameterizations {
            Self::for_each_param_group_rev(
                &TempStack::new_root(()),
                &parameterization.items,
                &mut |parameterizations, param_group| {
                    let mut parameterizations_rev = Vec::new();
                    for frame in parameterizations.iter() {
                        for parameterization in frame.iter().rev() {
                            Self::for_each_param_notation_rev(
                                &parameterization.items,
                                |_, notation| {
                                    parameterizations_rev.push(notation.expr.clone());
                                },
                            );
                        }
                    }
                    for notation in param_group.param_notations.iter().rev() {
                        param_notations_rev.push(NotationInfo {
                            parameterizations_rev: parameterizations_rev.clone(),
                            notation: (**notation).clone(),
                        });
                    }
                },
            );
        }

        let notation_ctx = NotationContext::new_root(());
        let notation_ctx = notation_ctx.new_frame(Either::Left(Either::Left(Either::Left(
            Either::Right(&self.open_sections),
        ))));
        let sub_ctx = notation_ctx.new_frame(Either::Left(Either::Left(Either::Left(
            Either::Left(&param_notations_rev),
        ))));

        let prefixes = Self::parse_prefixes(interface, section_kind, &sub_ctx);

        let (Some(item_header), _) = Self::parse_section_item_header(
            interface,
            section_kind,
            true,
            None,
            !parameterizations.is_empty(),
            !prefixes.is_empty(),
            &sub_ctx,
            NameScopeDesc::Global,
        ) else {
            if !parameterizations.is_empty() || !prefixes.is_empty() {
                let span = parameterizations.first().unwrap().span()
                    ..parameterizations.last().unwrap().span();
                interface.out(
                    span,
                    ParameterEvent::ParamGroup(Parameterized {
                        parameterizations,
                        prefixes,
                        data: None,
                    }),
                );
            }
            return false;
        };

        let mut span = item_header.span();
        if let Some(first) = parameterizations.first() {
            span.start = first.span().start;
        }

        let out = match item_header.into_inner() {
            SectionItemHeader::Section(kind) => {
                self.open_sections.push(OpenSection {
                    kind,
                    param_notations_rev,
                });
                ParameterEvent::SectionStart(Parameterized {
                    parameterizations,
                    prefixes,
                    data: Some(kind),
                })
            }
            SectionItemHeader::ParamGroup(param_group) => {
                ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes,
                    data: Some(param_group),
                })
            }
        };
        interface.out(span, out);

        false
    }
}

impl<'a> ParameterIdentifier<'a> {
    fn parse_metamodel<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
    ) -> bool {
        let input = interface.input();
        let Some(slate_keyword) = input.next() else {
            let pos = input.pos();
            interface.error(
                pos,
                Some(ErrorKind::SyntaxError),
                format!("expected keyword `%slate`"),
            );
            return true;
        };
        if !matches!(
            &*slate_keyword,
            TokenEvent::Token(Token::Keyword(keyword)) if keyword == "%slate"
        ) {
            interface.error(
                &slate_keyword,
                Some(ErrorKind::SyntaxError),
                format!("expected keyword `%slate`"),
            );
            return true;
        }
        let Some(metamodel_name_str) = input.next() else {
            let pos = input.pos();
            interface.error(
                pos,
                Some(ErrorKind::SyntaxError),
                format!("expected metamodel name"),
            );
            return true;
        };
        let TokenEvent::Token(Token::String('"', metamodel_name)) = &*metamodel_name_str else {
            interface.error(
                &metamodel_name_str,
                Some(ErrorKind::SyntaxError),
                format!("expected string"),
            );
            return true;
        };
        let found = interface.modify_config(|(_, config)| {
            config.metamodel = config.metamodel_getter.metamodel(metamodel_name.as_ref());
            config.metamodel.is_some()
        });
        if !found {
            interface.error(
                &metamodel_name_str,
                Some(ErrorKind::ResourceNotFound),
                format!("unknown metamodel {metamodel_name:?}"),
            );
        }
        if interface
            .input()
            .next_if(|token| matches!(token, TokenEvent::Token(Token::ReservedChar(';', _, _))))
            .is_none()
        {
            interface.error(
                metamodel_name_str.span().end,
                Some(ErrorKind::SyntaxError),
                format!("expected `;`"),
            );
        };
        return !found;
    }

    fn parse_section_items<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        section_kind: &'static dyn SectionKind,
        require_semicolon_after_last: bool,
        separator: Option<char>,
        notation_ctx: &NotationContext<'a, Pos>,
        scope: NameScopeDesc,
    ) -> SectionItems<'a, Pos> {
        let mut items = Vec::new();
        loop {
            let parameterizations = Self::parse_parameterizations(interface, section_kind);
            let sub_ctx = notation_ctx.new_frame(Either::Left(Either::Left(Either::Right(
                &parameterizations,
            ))));
            let prefixes = Self::parse_prefixes(interface, section_kind, &sub_ctx);
            let (item, finished) = Self::parse_section_item(
                interface,
                section_kind,
                require_semicolon_after_last,
                separator,
                !parameterizations.is_empty(),
                !prefixes.is_empty(),
                &sub_ctx,
                scope,
            );
            if item.is_some() || !parameterizations.is_empty() || !prefixes.is_empty() {
                items.push(Parameterized {
                    parameterizations,
                    prefixes,
                    data: item,
                });
            }
            if finished {
                break;
            }
        }
        items
    }

    fn parse_section_item<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        section_kind: &'static dyn SectionKind,
        require_semicolon_after_last: bool,
        separator: Option<char>,
        has_parameterizations: bool,
        has_prefixes: bool,
        notation_ctx: &NotationContext<'a, Pos>,
        scope: NameScopeDesc,
    ) -> (Option<SectionItem<'a, Pos>>, bool) {
        let (item_header, finished) = Self::parse_section_item_header(
            interface,
            section_kind,
            require_semicolon_after_last,
            separator,
            has_parameterizations,
            has_prefixes,
            notation_ctx,
            scope,
        );
        let Some(item_header) = item_header else {
            return (None, finished);
        };
        match item_header.into_inner() {
            SectionItemHeader::Section(kind) => {
                let items =
                    Self::parse_section_items(interface, kind, true, None, notation_ctx, scope);
                let end_token = interface.input().next().unwrap();
                assert_eq!(*end_token, TokenEvent::ParenEnd);
                (
                    Some(SectionItem::Section(Section { kind, items })),
                    finished,
                )
            }
            SectionItemHeader::ParamGroup(param_group) => {
                (Some(SectionItem::ParamGroup(param_group)), finished)
            }
        }
    }

    fn parse_section_item_header<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        section_kind: &'static dyn SectionKind,
        require_semicolon_after_last: bool,
        separator: Option<char>,
        has_parameterizations: bool,
        has_prefixes: bool,
        notation_ctx: &NotationContext<'a, Pos>,
        scope: NameScopeDesc,
    ) -> (Option<WithSpan<SectionItemHeader<'a, Pos>, Pos>>, bool) {
        {
            let no_item = |interface: &mut IF, pos: Option<Pos>| {
                if has_prefixes {
                    let pos = pos.unwrap_or_else(|| interface.input().pos());
                    interface.error(
                        pos,
                        Some(ErrorKind::SyntaxError),
                        format!("expected item after prefix"),
                    );
                    true
                } else if has_parameterizations {
                    let pos = pos.unwrap_or_else(|| interface.input().pos());
                    interface.error(
                        pos,
                        Some(ErrorKind::SyntaxError),
                        format!("expected item after parameterization"),
                    );
                    true
                } else {
                    false
                }
            };

            let Some(start_token) = interface.input().look_ahead() else {
                no_item(interface, None);
                return (None, true);
            };
            match *start_token {
                TokenEvent::Token(Token::ReservedChar(ch, _, _))
                    if ch == ';' || Some(ch) == separator =>
                {
                    let start_token = start_token.consume();
                    if !no_item(interface, Some(start_token.span().start)) && ch == ';' {
                        interface.error(
                            &start_token,
                            Some(ErrorKind::SyntaxError),
                            format!("superfluous semicolon"),
                        );
                    }
                    return (None, true);
                }
                TokenEvent::ParenStart(paren) => {
                    if let Some(subsection_kind) = section_kind.subsection(paren) {
                        let start_token = start_token.consume();
                        return (
                            Some(WithSpan::new(
                                SectionItemHeader::Section(subsection_kind),
                                &start_token,
                            )),
                            false,
                        );
                    }
                }
                TokenEvent::ParenEnd => {
                    drop(start_token);
                    no_item(interface, None);
                    return (None, true);
                }
                _ => {}
            }
        }

        let data_kind = section_kind.data_kind();
        let param_kind = section_kind.param_kind();

        let mut at_expr_start = true;
        let start_token = Self::parse_token_tree(interface, data_kind, at_expr_start).unwrap();
        at_expr_start = Self::token_tree_is_expr_prefix(&start_token);
        let mut span = start_token.span();
        let mut tokens = vec![start_token];
        let finished = loop {
            let Some(token) = Self::parse_token_tree(interface, data_kind, at_expr_start) else {
                if require_semicolon_after_last {
                    interface.error(
                        span.end.clone(),
                        Some(ErrorKind::SyntaxError),
                        format!("expected `;`"),
                    );
                }
                break true;
            };
            if matches!(*token, TokenTree::Token(Token::ReservedChar(';', _, _))) {
                break false;
            }
            if matches!(
                *token,
                TokenTree::Token(Token::ReservedChar(ch, _, _)) if Some(ch) == separator
            ) {
                break true;
            }
            at_expr_start = Self::token_tree_is_notation_delimiter(&token, param_kind).is_some()
                || Self::token_tree_is_expr_prefix(&token);
            span.end = token.span().end;
            tokens.push(token);
        };

        let prefix_options = if has_prefixes {
            section_kind.notation_prefixes()
        } else {
            None
        };

        let param_group = Self::create_param_group(
            interface,
            tokens,
            param_kind,
            &prefix_options,
            notation_ctx,
            scope,
        );

        (
            Some(WithSpan::new(
                SectionItemHeader::ParamGroup(param_group),
                span,
            )),
            finished,
        )
    }

    fn parse_parameterizations<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        section_kind: &'static dyn SectionKind,
    ) -> Vec<WithSpan<Parameterization<'a, Pos>, Pos>> {
        let empty_ctx = NotationContext::new_root(());
        let mut parameterizations = Vec::new();
        loop {
            let Some(start_token) = interface.input().look_ahead() else {
                break;
            };
            let TokenEvent::ParenStart(paren) = *start_token else {
                break;
            };
            let Some(kind) = section_kind.parameterization(paren) else {
                break;
            };
            let start_token = start_token.consume();
            let items = Self::parse_section_items(
                interface,
                kind,
                false,
                None,
                &empty_ctx,
                NameScopeDesc::Param,
            );
            let end_token = interface.input().next().unwrap();
            assert_eq!(*end_token, TokenEvent::ParenEnd);
            parameterizations.push(WithSpan::new(
                Parameterization { kind, items },
                &start_token..&end_token,
            ));
        }
        parameterizations
    }

    fn parse_prefixes<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        section_kind: &'static dyn SectionKind,
        notation_ctx: &NotationContext<'a, Pos>,
    ) -> Vec<WithSpan<NotationExpr<'a>, Pos>> {
        let data_kind = section_kind.data_kind();
        let mut prefixes = Vec::new();
        if let Some(options) = section_kind.notation_prefixes() {
            loop {
                let mut first = true;
                if Self::search_top_level_token(interface, |token| {
                    if first {
                        first = false;
                        if Self::token_event_matches_prefix_options(&token, &options, data_kind) {
                            None
                        } else {
                            Some(false)
                        }
                    } else {
                        Some(matches!(
                            token,
                            TokenEvent::Token(Token::ReservedChar('.', _, _))
                        ))
                    }
                }) != Some(true)
                {
                    break;
                }
                let token = Self::parse_token_tree(interface, data_kind, false).unwrap();
                let span = token.span();
                if let Some(prefix) =
                    Self::create_token_notation_expr(interface, token, notation_ctx)
                {
                    let prefix = Self::remove_prefix_parentheses(prefix, &options, true);
                    prefixes.push(WithSpan::new(prefix, span));
                }
                let dot = interface.input().next().unwrap();
                assert!(matches!(
                    *dot,
                    TokenEvent::Token(Token::ReservedChar('.', _, _))
                ));
            }
        }
        prefixes
    }

    fn parse_object_items<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        object_kind: &'static dyn ObjectKind,
    ) -> Vec<ObjectItem<'a, Pos>> {
        let separator = object_kind.separator();
        let parameterization_kind = object_kind.parameterization();
        let param_data_kind = object_kind.param_data_kind();
        let empty_ctx = NotationContext::new_root(());
        let mut items = Vec::new();
        while let Some(token) = Self::parse_token_tree(interface, param_data_kind, false) {
            let mut param_tokens = Vec::new();
            if Self::token_tree_is_reserved_char(&token, separator) {
                interface.error(
                    &token,
                    Some(ErrorKind::SyntaxError),
                    format!("superfluous separator"),
                );
            } else {
                param_tokens.push(token);
            }
            let mut parameterization_items = Vec::new();
            let mut extra_parts = Vec::new();
            while let Some(token) = Self::parse_token_tree(interface, param_data_kind, false) {
                if Self::token_tree_is_reserved_char(&token, separator) {
                    parameterization_items = Self::parse_section_items(
                        interface,
                        parameterization_kind,
                        false,
                        Some(separator),
                        &empty_ctx,
                        NameScopeDesc::Field,
                    );
                    if !parameterization_items.is_empty() {
                        loop {
                            if let Some(extra_part_kind) =
                                object_kind.extra_part_kind(extra_parts.len())
                            {
                                let extra_part_items = Self::parse_section_items(
                                    interface,
                                    extra_part_kind,
                                    false,
                                    Some(separator),
                                    &empty_ctx,
                                    NameScopeDesc::Instance,
                                );
                                if extra_part_items.is_empty() {
                                    break;
                                }
                                extra_parts.push(extra_part_items);
                            } else {
                                let Some(span) =
                                    Self::skip_until_top_level_token(interface, |token| {
                                        matches!(
                                            token,
                                            TokenEvent::Token(Token::ReservedChar(ch, _, _))
                                                if *ch == separator
                                        )
                                    })
                                else {
                                    break;
                                };
                                interface.error(
                                    span,
                                    Some(ErrorKind::SyntaxError),
                                    format!("superfluous item part"),
                                );
                            }
                        }
                    }
                    break;
                } else {
                    param_tokens.push(token);
                }
            }
            let parameterization = Parameterization {
                kind: parameterization_kind,
                items: parameterization_items,
            };
            let sub_ctx = empty_ctx.new_frame(Either::Left(Either::Right(&parameterization)));
            let param = Self::create_param(
                interface,
                &mut param_tokens,
                object_kind.param_kind(),
                &sub_ctx,
                NameScopeDesc::Instance,
            );
            items.push(ObjectItem {
                parameterization,
                param,
                extra_parts,
            })
        }
        items
    }

    fn parse_token_tree<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        data_kind: &'static dyn DataKind,
        at_expr_start: bool,
    ) -> Option<WithSpan<TokenTree<'a, Pos>, Pos>> {
        let start_token = interface
            .input()
            .next_if(|token| *token != TokenEvent::ParenEnd)?;
        let mut span = start_token.span();
        match start_token.into_inner() {
            TokenEvent::ParenStart(paren) => {
                if at_expr_start {
                    if let Some(parameterization) = data_kind.parameterization(paren) {
                        let param_kind = parameterization.param_kind();
                        if Self::search_top_level_token(interface, |token| {
                            if Self::token_event_is_notation_delimiter(token, param_kind).is_some()
                            {
                                Some(true)
                            } else {
                                None
                            }
                        }) == Some(true)
                        {
                            let items = Self::parse_section_items(
                                interface,
                                parameterization,
                                false,
                                None,
                                &NotationContext::new_root(()),
                                NameScopeDesc::Local,
                            );
                            let end_token = interface.input().next().unwrap();
                            assert_eq!(*end_token, TokenEvent::ParenEnd);
                            span.end = end_token.span().end;
                            return Some(WithSpan::new(
                                TokenTree::Parameterization(Parameterization {
                                    kind: parameterization,
                                    items,
                                }),
                                span,
                            ));
                        }
                    }
                }
                if let Some(object_kind) = data_kind.object_kind(paren) {
                    let items = Self::parse_object_items(interface, object_kind);
                    let end_token = interface.input().next().unwrap();
                    assert_eq!(*end_token, TokenEvent::ParenEnd);
                    span.end = end_token.span().end;
                    return Some(WithSpan::new(
                        TokenTree::Object(Object {
                            kind: object_kind,
                            items,
                        }),
                        span,
                    ));
                }
                let inner_data_kind = data_kind.special_data_kind(paren).unwrap_or(data_kind);
                let mut tokens = Vec::new();
                loop {
                    let (expr_tokens, punct) =
                        Self::parse_expr_within_parentheses(interface, inner_data_kind);
                    tokens.extend(expr_tokens);
                    let Some(punct) = punct else { break };
                    tokens.push(punct);
                }
                let end_token = interface.input().next().unwrap();
                assert_eq!(*end_token, TokenEvent::ParenEnd);
                span.end = end_token.span().end;
                Some(WithSpan::new(TokenTree::Paren(paren, tokens), span))
            }
            TokenEvent::ParenEnd => unreachable!(),
            TokenEvent::Token(token) => {
                if let Token::Ident(identifier, IdentifierType::Unquoted) = &token {
                    if let Some(mapping_kind) = data_kind.prefix_mapping_kind(identifier) {
                        let mut param_tokens = Vec::new();
                        let dot_found = loop {
                            let Some(token) = interface.input().look_ahead() else {
                                break false;
                            };
                            if matches!(*token, TokenEvent::Token(Token::ReservedChar(';', _, _))) {
                                break false;
                            }
                            drop(token);
                            let Some(token) = Self::parse_token_tree(interface, data_kind, false)
                            else {
                                break false;
                            };
                            span.end = token.span().end;
                            if matches!(*token, TokenTree::Token(Token::ReservedChar('.', _, _))) {
                                break true;
                            }
                            param_tokens.push(token);
                        };
                        if !dot_found {
                            interface.error(
                                span.end.clone(),
                                Some(ErrorKind::SyntaxError),
                                format!("expected `.`"),
                            );
                        }
                        let params = Self::create_mapping_params(
                            interface,
                            &mut param_tokens,
                            mapping_kind.param_kind(),
                            &NotationContext::new_root(()),
                        );
                        return Some(WithSpan::new(
                            TokenTree::Mapping(Mapping {
                                kind: mapping_kind,
                                params,
                            }),
                            span,
                        ));
                    }
                }
                Some(WithSpan::new(TokenTree::Token(token), span))
            }
        }
    }

    fn parse_expr_within_parentheses<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        data_kind: &'static dyn DataKind,
    ) -> (Tokens<'a, Pos>, Option<WithSpan<TokenTree<'a, Pos>, Pos>>) {
        let mut expr_tokens = Vec::new();
        let mut token_at_expr_start = true;
        while let Some(token) = Self::parse_token_tree(interface, data_kind, token_at_expr_start) {
            if matches!(
                *token,
                TokenTree::Token(Token::ReservedChar(',', _, _))
                    | TokenTree::Token(Token::ReservedChar(';', _, _))
                    | TokenTree::Parameterization(_)
            ) {
                return (expr_tokens, Some(token));
            }
            if let Some(first_expr_token) = expr_tokens.first() {
                if let TokenTree::Token(Token::Ident(identifier, IdentifierType::Unquoted)) =
                    &*token
                {
                    if let Some(mapping_kind) = data_kind.infix_mapping_kind(identifier) {
                        let mapping_span = (first_expr_token..&token).span();
                        if expr_tokens.len() == 1
                            && matches!(
                                **first_expr_token,
                                TokenTree::Paren(paren, _)
                                    if paren == mapping_kind.binder_paren()
                            )
                        {
                            let expr_token = expr_tokens.into_iter().next().unwrap();
                            let TokenTree::Paren(_, inner) = expr_token.into_inner() else {
                                unreachable!()
                            };
                            expr_tokens = inner;
                        }
                        let params = Self::create_mapping_params(
                            interface,
                            &mut expr_tokens,
                            mapping_kind.param_kind(),
                            &NotationContext::new_root(()),
                        );
                        let mapping_token = WithSpan::new(
                            TokenTree::Mapping(Mapping {
                                kind: mapping_kind.as_mapping_kind(),
                                params,
                            }),
                            mapping_span,
                        );
                        let (mut tokens, punct) =
                            Self::parse_expr_within_parentheses(interface, data_kind);
                        tokens.insert(0, mapping_token);
                        return (tokens, punct);
                    }
                }
            }
            token_at_expr_start = Self::token_tree_is_expr_prefix(&token);
            expr_tokens.push(token);
        }
        (expr_tokens, None)
    }

    fn create_param_group<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        mut tokens: Tokens<'a, Pos>,
        param_kind: &'static dyn ParamKind,
        prefix_options: &Option<NotationPrefixOptions>,
        notation_ctx: &NotationContext<'a, Pos>,
        scope: NameScopeDesc,
    ) -> ParamGroup<'a, Pos> {
        let mut param_notations = Vec::new();

        let notation_delimiter_found = tokens.iter().find_map(|token| {
            if Self::token_tree_is_notation_delimiter(&token, param_kind).is_some() {
                Some(true)
            } else if matches!(
                **token,
                TokenTree::Token(Token::Keyword(_)) | TokenTree::Token(Token::String(_, _))
            ) {
                Some(false)
            } else {
                None
            }
        });
        if notation_delimiter_found == Some(true) {
            let mut token_iter = take(&mut tokens).into_iter();
            while let Some(token) = token_iter.next() {
                let is_comma = matches!(*token, TokenTree::Token(Token::ReservedChar(',', _, _)));
                let notation_delimiter_desc =
                    Self::token_tree_is_notation_delimiter(&token, param_kind);
                if is_comma || notation_delimiter_desc.is_some() {
                    if tokens.is_empty() {
                        interface.error(
                            token.span().start,
                            Some(ErrorKind::SyntaxError),
                            format!("expected name/notation"),
                        );
                    } else {
                        if let Some(notation) = Self::create_notation(
                            interface,
                            &mut tokens,
                            prefix_options,
                            notation_ctx,
                            scope,
                            notation_delimiter_desc.unwrap_or(None),
                        ) {
                            param_notations.push(notation);
                        }
                    }
                    if !is_comma {
                        tokens.push(token);
                        tokens.extend(token_iter);
                        break;
                    }
                } else {
                    tokens.push(token);
                }
            }
        }

        if prefix_options.is_some() && param_notations.len() > 1 {
            interface.error(
                param_notations.first().unwrap()..param_notations.last().unwrap(),
                Some(ErrorKind::SyntaxError),
                format!("a parameter group with a prefix cannot contain multiple parameters"),
            );
        }

        ParamGroup {
            param_notations,
            data: tokens,
        }
    }

    fn create_mapping_params<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        tokens: &mut Tokens<'a, Pos>, // will be drained (intentionally not moved to reuse vector allocations)
        param_kind: &'static dyn ParamKind,
        notation_ctx: &NotationContext<'a, Pos>,
    ) -> Vec<MappingParam<'a, Pos>> {
        let mut params = Vec::new();

        let mut param_tokens = Vec::new();
        for token in tokens.drain(..) {
            let mut is_comma = matches!(*token, TokenTree::Token(Token::ReservedChar(',', _, _)));
            if matches!(*token, TokenTree::Token(Token::ReservedChar(';', _, _))) {
                interface.error(
                    &token,
                    Some(ErrorKind::SyntaxError),
                    format!("expected `,` instead of `;`"),
                );
                is_comma = true;
            }
            if is_comma {
                if param_tokens.is_empty() {
                    interface.error(
                        &token,
                        Some(ErrorKind::SyntaxError),
                        format!("superfluous comma"),
                    );
                } else {
                    params.push(Self::create_mapping_param(
                        interface,
                        &mut param_tokens,
                        param_kind,
                        notation_ctx,
                    ));
                }
            } else {
                param_tokens.push(token);
            }
        }
        if !param_tokens.is_empty() {
            params.push(Self::create_mapping_param(
                interface,
                &mut param_tokens,
                param_kind,
                notation_ctx,
            ));
        }

        params
    }

    fn create_mapping_param<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        tokens: &mut Tokens<'a, Pos>, // will be drained (intentionally not moved to reuse vector allocations)
        param_kind: &'static dyn ParamKind,
        notation_ctx: &NotationContext<'a, Pos>,
    ) -> MappingParam<'a, Pos> {
        if let Some(token) = tokens.first() {
            if matches!(**token, TokenTree::Mapping(_)) {
                let token = tokens.remove(0);
                let TokenTree::Mapping(mapping) = token.into_inner() else {
                    unreachable!()
                };
                let sub_ctx = notation_ctx.new_frame(Either::Right(&mapping.params));
                let mut param = Self::create_mapping_param(interface, tokens, param_kind, &sub_ctx);
                param.mappings.insert(0, mapping);
                return param;
            }
        }

        let param = Self::create_param(
            interface,
            tokens,
            param_kind,
            notation_ctx,
            NameScopeDesc::Param,
        );
        MappingParam {
            mappings: Vec::new(),
            notation: param.notation,
            data: param.data,
        }
    }

    fn create_param<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        tokens: &mut Tokens<'a, Pos>, // will be drained (intentionally not moved to reuse vector allocations)
        param_kind: &'static dyn ParamKind,
        notation_ctx: &NotationContext<'a, Pos>,
        scope: NameScopeDesc,
    ) -> Param<'a, Pos> {
        let mut notation = Vec::new();
        let mut data = Vec::new();
        let mut kind = None;

        let mut token_iter = tokens.drain(..);
        while let Some(token) = token_iter.next() {
            let notation_delimiter_desc =
                Self::token_tree_is_notation_delimiter(&token, param_kind);
            if let Some(kind_override) = notation_delimiter_desc {
                if notation.is_empty() {
                    interface.error(
                        token.span().start,
                        Some(ErrorKind::SyntaxError),
                        format!("expected name/notation"),
                    );
                }
                data.push(token);
                data.extend(token_iter);
                kind = kind_override;
                break;
            }
            notation.push(token);
        }

        Param {
            notation: Self::create_notation(
                interface,
                &mut notation,
                &None,
                notation_ctx,
                scope,
                kind,
            ),
            data,
        }
    }

    fn create_notation<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        tokens: &mut Tokens<'a, Pos>, // will be drained (intentionally not moved to reuse vector allocations)
        prefix_options: &Option<NotationPrefixOptions>,
        notation_ctx: &NotationContext<'a, Pos>,
        scope: NameScopeDesc,
        mut kind: Option<NameKindDesc>,
    ) -> Option<WithSpan<Notation<'a>, Pos>> {
        if tokens.is_empty() {
            return None;
        }

        if kind.is_some() && Self::is_notation_parameterized(notation_ctx) {
            match kind {
                Some(NameKindDesc::Value) => kind = Some(NameKindDesc::Function),
                Some(NameKindDesc::Type) => kind = Some(NameKindDesc::GenericType),
                _ => {}
            }
        }

        let span = (tokens.first().unwrap()..tokens.last().unwrap()).span();
        interface.span_desc(span.clone(), SpanDesc::NameDef(scope, kind));

        if prefix_options.is_some() {
            let mut prev_is_ident = false;
            for token in tokens.iter() {
                if matches!(
                    **token,
                    TokenTree::Token(Token::Ident(_, _)) | TokenTree::Token(Token::Number(_))
                ) {
                    if prev_is_ident {
                        interface.error(
                            span.clone(),
                            Some(ErrorKind::SyntaxError),
                            format!("a prefixed notation with an identifier sequence must be wrapped in parentheses"),
                        );
                        break;
                    }
                    prev_is_ident = true;
                } else {
                    prev_is_ident = false;
                }
            }
        }

        let mut expr = Self::create_notation_expr(interface, tokens, notation_ctx)?;

        if let Some(prefix_options) = prefix_options {
            expr = Self::remove_prefix_parentheses(expr, prefix_options, false);
        }

        if matches!(expr, NotationExpr::Param(_)) {
            interface.error(
                span,
                Some(ErrorKind::SyntaxError),
                format!("a notation cannot consist entirely of a parameter"),
            );
            return None;
        }

        Some(WithSpan::new(Notation { expr, scope, kind }, span))
    }

    fn create_notation_expr<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        tokens: &mut Tokens<'a, Pos>, // will be drained (intentionally not moved to reuse vector allocations)
        notation_ctx: &NotationContext<'a, Pos>,
    ) -> Option<NotationExpr<'a>> {
        if tokens.len() > 1 {
            let span = (tokens.first().unwrap()..tokens.last().unwrap()).span();
            let mut exprs = Vec::new();
            let mut spans = Vec::new();
            let mut token_iter = tokens.drain(..);
            while let Some(token) = token_iter.next() {
                if let TokenTree::Mapping(mapping) = &*token {
                    let mut mapping_span = token.span();
                    let mut target_span = mapping_span.clone();
                    let mut target_tokens: Tokens<'a, Pos> = token_iter.collect();
                    if let Some(last_token) = target_tokens.last() {
                        mapping_span.end = last_token.span().end;
                        target_span = (target_tokens.first().unwrap()..last_token).span();
                    }
                    for param in &mapping.params {
                        if !param.data.is_empty() {
                            interface.error(
                                param.data.first().unwrap()..param.data.last().unwrap(),
                                Some(ErrorKind::SyntaxError),
                                format!("a mapping parameter within a notation cannot be followed by additional data"),
                            );
                        }
                    }
                    let sub_ctx = notation_ctx.new_frame(Either::Right(&mapping.params));
                    if let Some(target_expr) =
                        Self::create_notation_expr(interface, &mut target_tokens, &sub_ctx)
                    {
                        if target_expr.contains_param_ref(-(mapping.params.len() as isize)..0) {
                            interface.error(
                                target_span,
                                Some(ErrorKind::SyntaxError),
                                format!("a mapping target within a notation cannot reference a standalone mapping parameter"),
                            );
                        }
                        exprs.push(NotationExpr::Mapping(Box::new(MappingNotationExpr {
                            kind: mapping.kind,
                            params_len: mapping.params.len(),
                            target_expr,
                        })));
                        spans.push(mapping_span);
                    }
                    break;
                }
                let token_span = token.span();
                if let Some(expr) =
                    Self::create_token_notation_expr_impl(interface, token, notation_ctx)
                {
                    exprs.push(expr);
                    spans.push(token_span);
                }
            }
            while let Some((range, param_idx, param_scope, param_kind)) =
                Self::identify_notation(interface, &exprs, span.clone(), notation_ctx)
            {
                let param_span = spans[range.start].start.clone()..spans[range.end - 1].end.clone();
                interface.span_desc(
                    param_span.clone(),
                    SpanDesc::NameRef(param_scope, param_kind),
                );
                if range == (0..exprs.len()) {
                    return Some(NotationExpr::Param(param_idx));
                }
                exprs.drain((range.start + 1)..range.end);
                exprs[range.start] = NotationExpr::Param(param_idx);
                spans.drain((range.start + 1)..range.end);
                spans[range.start] = param_span;
            }
            if exprs.len() == 1 {
                Some(exprs.pop().unwrap())
            } else {
                Some(NotationExpr::Seq(exprs))
            }
        } else {
            let token = tokens.drain(..).next()?;
            Self::create_token_notation_expr(interface, token, notation_ctx)
        }
    }

    fn create_token_notation_expr<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        token: WithSpan<TokenTree<'a, Pos>, Pos>,
        notation_ctx: &NotationContext<'a, Pos>,
    ) -> Option<NotationExpr<'a>> {
        let span = token.span();
        let expr = Self::create_token_notation_expr_impl(interface, token, notation_ctx)?;
        if let Some((_, param_idx, param_scope, param_kind)) = Self::identify_notation(
            interface,
            slice::from_ref(&expr),
            span.clone(),
            notation_ctx,
        ) {
            interface.span_desc(span, SpanDesc::NameRef(param_scope, param_kind));
            Some(NotationExpr::Param(param_idx))
        } else {
            Some(expr)
        }
    }

    fn create_token_notation_expr_impl<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        token: WithSpan<TokenTree<'a, Pos>, Pos>,
        notation_ctx: &NotationContext<'a, Pos>,
    ) -> Option<NotationExpr<'a>> {
        let span = token.span();
        match token.into_inner() {
            TokenTree::Token(token) => match token {
                Token::ReservedChar(ch, _, _) => Some(NotationExpr::ReservedChar(ch)),
                Token::Keyword(_) => {
                    interface.error(
                        span,
                        Some(ErrorKind::SyntaxError),
                        format!("a keyword cannot be part of a notation"),
                    );
                    None
                }
                Token::Number(number) => Some(NotationExpr::Ident(number)),
                Token::String(_, _) => {
                    interface.error(
                        span,
                        Some(ErrorKind::SyntaxError),
                        format!("a string cannot be part of a notation"),
                    );
                    None
                }
                Token::Ident(identifier, _) => Some(NotationExpr::Ident(identifier)),
            },

            TokenTree::Paren(paren, inner) => {
                let mut rows = Vec::new();
                let mut cols = Vec::new();
                let mut tokens = Vec::new();
                for token in inner {
                    if matches!(*token, TokenTree::Token(Token::ReservedChar(',', _, _))) {
                        if tokens.is_empty() {
                            interface.error(
                                &token,
                                Some(ErrorKind::SyntaxError),
                                format!("superfluous comma"),
                            );
                        } else if let Some(expr) =
                            Self::create_notation_expr(interface, &mut tokens, notation_ctx)
                        {
                            cols.push(expr);
                        }
                    } else if matches!(*token, TokenTree::Token(Token::ReservedChar(';', _, _))) {
                        if !tokens.is_empty() {
                            if let Some(expr) =
                                Self::create_notation_expr(interface, &mut tokens, notation_ctx)
                            {
                                cols.push(expr);
                            }
                        }
                        if cols.is_empty() {
                            interface.error(
                                &token,
                                Some(ErrorKind::SyntaxError),
                                format!("superfluous semicolon"),
                            );
                        } else {
                            rows.push(take(&mut cols));
                        }
                    } else {
                        tokens.push(token);
                    }
                }
                if !tokens.is_empty() {
                    if let Some(expr) =
                        Self::create_notation_expr(interface, &mut tokens, notation_ctx)
                    {
                        cols.push(expr);
                    }
                }
                if !cols.is_empty() {
                    rows.push(cols);
                }
                Some(NotationExpr::Paren(paren, rows))
            }

            _ => {
                interface.error(
                    span,
                    Some(ErrorKind::SyntaxError),
                    format!("this expression cannot be part of a notation"),
                );
                None
            }
        }
    }

    fn remove_prefix_parentheses(
        expr: NotationExpr<'a>,
        options: &NotationPrefixOptions,
        allow_single_param: bool,
    ) -> NotationExpr<'a> {
        if let NotationExpr::Paren(paren, inner) = &expr {
            if *paren == options.paren && inner.len() == 1 {
                let row = inner.first().unwrap();
                if row.len() == 1 {
                    if allow_single_param || !matches!(row.first().unwrap(), NotationExpr::Param(_))
                    {
                        let NotationExpr::Paren(_, inner) = expr else {
                            unreachable!()
                        };
                        return inner
                            .into_iter()
                            .next()
                            .unwrap()
                            .into_iter()
                            .next()
                            .unwrap();
                    }
                }
            }
        }
        expr
    }

    fn identify_notation<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        seq: &[NotationExpr<'a>],
        span: Range<Pos>,
        notation_ctx: &NotationContext<'a, Pos>,
    ) -> Option<(Range<usize>, ParamIdx, NameScopeDesc, Option<NameKindDesc>)> {
        let mut range = None;
        let mut result = None;
        Self::for_each_valid_notation(notation_ctx, |idx, notation, mapping_mismatches| {
            if let Some(notation_range) = notation.expr.find_in_sequence(seq) {
                if let Some(range) = &mut range {
                    match range_overlap(range, &notation_range) {
                        RangeOverlap::Disjoint | RangeOverlap::Exact | RangeOverlap::Narrowing => {}
                        RangeOverlap::Widening => {
                            *range = notation_range;
                            result = Some((idx, notation.scope, notation.kind, mapping_mismatches));
                        }
                        RangeOverlap::Overlapping => {
                            *range = notation_range;
                            result = None;
                        }
                    }
                } else {
                    range = Some(notation_range);
                    result = Some((idx, notation.scope, notation.kind, mapping_mismatches));
                }
            }
        });
        if let Some(range) = range {
            if let Some((param_idx, param_scope, param_kind, mapping_mismatches)) = result {
                let mut mapping_notation_ctx = notation_ctx;
                let mut mapping_param_idx = 0;
                for (mapping_mismatch_param_idx, mapping_mismatch_notation) in mapping_mismatches {
                    'find_param: while let NotationContext::Frame { data, parent } =
                        mapping_notation_ctx
                    {
                        let NotationContextFrame::Mapping(params) = data else {
                            unreachable!();
                        };
                        for param in params.iter().rev() {
                            mapping_param_idx -= 1;
                            if mapping_param_idx == mapping_mismatch_param_idx {
                                let msg = if let NotationExpr::Ident(identifier) =
                                    mapping_mismatch_notation
                                {
                                    format!("mapping parameter name does not match parameterization; expected `{identifier}`")
                                } else {
                                    format!("mapping parameter notation does not match parameterization")
                                };
                                interface.warning(
                                    param.notation.as_ref().unwrap().span(),
                                    Some(WarningKind::SyntaxWarning),
                                    msg,
                                );
                                break 'find_param;
                            }
                        }
                        mapping_notation_ctx = &*parent;
                    }
                }
                return Some((range, param_idx, param_scope, param_kind));
            } else {
                interface.error(
                    span,
                    Some(ErrorKind::SyntaxError),
                    format!("ambiguous parameter references in notation"),
                );
            }
        }
        None
    }

    fn for_each_notation<Pos: Position>(
        mut notation_ctx: &NotationContext<'a, Pos>,
        mut f: impl FnMut(usize, ParameterizationNotations<'a, '_, Pos>, &Notation<'a>),
    ) {
        let mut cur_idx = 0;
        while let NotationContext::Frame { data, parent } = notation_ctx {
            match data {
                NotationContextFrame::DirectRev(notation_infos_rev) => {
                    for notation_info in &**notation_infos_rev {
                        f(
                            cur_idx,
                            ParameterizationNotations::DirectRev(
                                &notation_info.parameterizations_rev,
                            ),
                            &notation_info.notation,
                        );
                        cur_idx += 1;
                    }
                }
                NotationContextFrame::OpenSections(open_sections) => {
                    for open_section in open_sections.iter().rev() {
                        for notation_info in &open_section.param_notations_rev {
                            f(
                                cur_idx,
                                ParameterizationNotations::DirectRev(
                                    &notation_info.parameterizations_rev,
                                ),
                                &notation_info.notation,
                            );
                            cur_idx += 1;
                        }
                    }
                }
                NotationContextFrame::Parameterizations(parameterizations) => {
                    for parameterization in parameterizations.iter().rev() {
                        Self::for_each_param_notation_rev(
                            &parameterization.items,
                            |parameterizations, notation| {
                                f(
                                    cur_idx,
                                    ParameterizationNotations::Parameterizations(parameterizations),
                                    notation,
                                );
                                cur_idx += 1;
                            },
                        );
                    }
                }
                NotationContextFrame::Parameterization(parameterization) => {
                    Self::for_each_param_notation_rev(
                        &parameterization.items,
                        |parameterizations, notation| {
                            f(
                                cur_idx,
                                ParameterizationNotations::Parameterizations(parameterizations),
                                notation,
                            );
                            cur_idx += 1;
                        },
                    );
                }
                NotationContextFrame::Mapping(params) => {
                    for param in params.iter().rev() {
                        if let Some(notation) = &param.notation {
                            f(
                                cur_idx,
                                ParameterizationNotations::Mappings(&param.mappings),
                                notation,
                            );
                        }
                        cur_idx += 1;
                    }
                }
            }
            notation_ctx = &*parent;
        }
    }

    fn for_each_valid_notation<Pos: Position>(
        notation_ctx: &NotationContext<'a, Pos>,
        mut f: impl FnMut(isize, &Notation<'a>, Vec<(isize, NotationExpr<'a>)>),
    ) {
        let mapping_len = Self::mapping_len(notation_ctx);
        Self::for_each_notation(notation_ctx, |idx, parameterizations, notation| {
            if idx < mapping_len {
                f(!(idx as isize), notation, Vec::new());
            } else {
                let mut parameterizations_len = 0;
                let mut mapping_mismatches = Vec::new();
                let mut mapping_notation_ctx = notation_ctx;
                let mut mapping_notation_param_idx = 0;
                parameterizations.for_each_notation_rev(|notation| {
                    loop {
                        let NotationContext::Frame { data, parent } = mapping_notation_ctx else {
                            break;
                        };
                        let NotationContextFrame::Mapping(params) = data else {
                            break;
                        };
                        if mapping_notation_param_idx < params.len() {
                            mapping_notation_param_idx += 1;
                            if let Some(notation) = notation {
                                let param = &params[params.len() - mapping_notation_param_idx];
                                if let Some(param_notation) = &param.notation {
                                    if param_notation.expr != *notation {
                                        mapping_mismatches.push((
                                            !(parameterizations_len as isize),
                                            notation.clone(),
                                        ));
                                    }
                                }
                            }
                            break;
                        } else {
                            mapping_notation_ctx = parent;
                            mapping_notation_param_idx = 0;
                        }
                    }
                    parameterizations_len += 1;
                });
                if parameterizations_len == mapping_len {
                    f(!(idx as isize), notation, mapping_mismatches);
                }
            }
        });
    }

    fn mapping_len<Pos: Position>(mut notation_ctx: &NotationContext<'a, Pos>) -> usize {
        let mut result = 0;
        while let NotationContext::Frame { data, parent } = notation_ctx {
            let NotationContextFrame::Mapping(params) = data else {
                break;
            };
            result += params.len();
            notation_ctx = &*parent;
        }
        result
    }

    fn is_notation_parameterized<Pos: Position>(
        mut notation_ctx: &NotationContext<'a, Pos>,
    ) -> bool {
        while let NotationContext::Frame { data, parent } = notation_ctx {
            match data {
                NotationContextFrame::DirectRev(notation_infos_rev) => {
                    if !notation_infos_rev.is_empty() {
                        return true;
                    }
                }
                NotationContextFrame::OpenSections(open_sections) => {
                    if open_sections
                        .iter()
                        .any(|open_section| !open_section.param_notations_rev.is_empty())
                    {
                        return true;
                    }
                }
                NotationContextFrame::Parameterizations(parameterizations) => {
                    for parameterization in parameterizations.iter().rev() {
                        let mut result = false;
                        Self::for_each_param_notation_rev(&parameterization.items, |_, _| {
                            result = true;
                        });
                        if result {
                            return true;
                        }
                    }
                }
                NotationContextFrame::Parameterization(parameterization) => {
                    let mut result = false;
                    Self::for_each_param_notation_rev(&parameterization.items, |_, _| {
                        result = true;
                    });
                    if result {
                        return true;
                    }
                }
                NotationContextFrame::Mapping(params) => {
                    if !params.is_empty() {
                        return true;
                    }
                }
            }
            notation_ctx = &*parent;
        }
        false
    }

    fn for_each_param_group_rev<Pos: Position>(
        parameterizations: &TempStack<(), TempRef<[WithSpan<Parameterization<'a, Pos>, Pos>]>>,
        section_items: &[Parameterized<'a, Pos, SectionItem<'a, Pos>>],
        f: &mut impl FnMut(
            &TempStack<(), TempRef<[WithSpan<Parameterization<'a, Pos>, Pos>]>>,
            &ParamGroup<'a, Pos>,
        ),
    ) {
        for item in section_items.iter().rev() {
            let sub_parameterizations = parameterizations.new_frame(&item.parameterizations);
            if let Some(data) = &item.data {
                match data {
                    SectionItem::Section(section) => {
                        Self::for_each_param_group_rev(&sub_parameterizations, &section.items, f)
                    }
                    SectionItem::ParamGroup(param_group) => {
                        f(&sub_parameterizations, param_group);
                    }
                }
            }
        }
    }

    fn for_each_param_notation_rev<Pos: Position>(
        section_items: &[Parameterized<'a, Pos, SectionItem<'a, Pos>>],
        mut f: impl FnMut(
            &TempStack<(), TempRef<[WithSpan<Parameterization<'a, Pos>, Pos>]>>,
            &Notation<'a>,
        ),
    ) {
        Self::for_each_param_group_rev(
            &TempStack::new_root(()),
            section_items,
            &mut |parameterizations, param_group| {
                for notation in param_group.param_notations.iter().rev() {
                    f(parameterizations, notation);
                }
            },
        )
    }

    fn skip_until_top_level_token<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        mut pred: impl FnMut(&TokenEvent<'a>) -> bool,
    ) -> Option<Range<Pos>> {
        let input = interface.input();
        let mut span: Option<Range<Pos>> = None;
        while let Some(token) = input.next_if(|token| !matches!(token, TokenEvent::ParenEnd)) {
            if pred(&*token) {
                break;
            }
            if let Some(span) = &mut span {
                span.end = token.span().end;
            } else {
                span = Some(token.span());
            }
            if matches!(*token, TokenEvent::ParenStart(_)) {
                let mut depth: usize = 0;
                loop {
                    let token = input.next().unwrap();
                    match *token {
                        TokenEvent::ParenStart(_) => {
                            depth += 1;
                        }
                        TokenEvent::ParenEnd => {
                            if depth > 0 {
                                depth -= 1;
                            } else {
                                span.as_mut().unwrap().end = token.span().end;
                                break;
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        span
    }

    fn search_top_level_token<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        mut pred: impl FnMut(&TokenEvent<'a>) -> Option<bool>,
    ) -> Option<bool> {
        let mut depth: usize = 0;
        interface.input().look_ahead_unbounded(|token| {
            if depth == 0 {
                let result = pred(token);
                if result.is_some() {
                    return result;
                }
            }
            match token {
                TokenEvent::ParenStart(_) => {
                    depth += 1;
                    None
                }
                TokenEvent::ParenEnd => {
                    if depth > 0 {
                        depth -= 1;
                        None
                    } else {
                        Some(false)
                    }
                }
                _ => None,
            }
        })
    }

    fn token_tree_is_reserved_char<Pos: Position>(token: &TokenTree<'a, Pos>, ch: char) -> bool {
        matches!(token, TokenTree::Token(Token::ReservedChar(c, _, _)) if *c == ch)
    }

    fn token_tree_is_expr_prefix<Pos: Position>(token: &TokenTree<'a, Pos>) -> bool {
        matches!(
            *token,
            TokenTree::Parameterization(_) | TokenTree::Mapping(_)
        )
    }

    fn token_tree_is_notation_delimiter<Pos: Position>(
        token: &TokenTree<'a, Pos>,
        param_kind: &'static dyn ParamKind,
    ) -> Option<NotationDelimiterDesc> {
        match token {
            TokenTree::Token(Token::Keyword(keyword)) => {
                param_kind.keyword_is_notation_delimiter(keyword)
            }
            TokenTree::Token(Token::Ident(identifier, IdentifierType::Unquoted)) => {
                param_kind.identifier_is_notation_delimiter(identifier)
            }
            TokenTree::Paren(paren, _) => param_kind.paren_is_notation_delimiter(*paren),
            _ => None,
        }
    }

    fn token_event_is_notation_delimiter(
        token: &TokenEvent<'a>,
        param_kind: &'static dyn ParamKind,
    ) -> Option<NotationDelimiterDesc> {
        match token {
            TokenEvent::Token(Token::Keyword(keyword)) => {
                param_kind.keyword_is_notation_delimiter(keyword)
            }
            TokenEvent::Token(Token::Ident(identifier, IdentifierType::Unquoted)) => {
                param_kind.identifier_is_notation_delimiter(identifier)
            }
            TokenEvent::ParenStart(paren) => param_kind.paren_is_notation_delimiter(*paren),
            _ => None,
        }
    }

    fn token_event_matches_prefix_options(
        token: &TokenEvent<'a>,
        options: &NotationPrefixOptions,
        data_kind: &'static dyn DataKind,
    ) -> bool {
        match token {
            TokenEvent::Token(Token::Ident(identifier, IdentifierType::Unquoted)) => {
                data_kind.prefix_mapping_kind(identifier).is_none()
            }
            TokenEvent::Token(Token::Ident(_, _)) | TokenEvent::Token(Token::Number(_)) => true,
            TokenEvent::ParenStart(paren) => *paren == options.paren,
            _ => false,
        }
    }
}

#[derive(MemSerializable)]
struct OpenSection<'a> {
    kind: &'static dyn SectionKind,
    param_notations_rev: Vec<NotationInfo<'a>>,
}

enum SectionItemHeader<'a, Pos: Position> {
    Section(&'static dyn SectionKind),
    ParamGroup(ParamGroup<'a, Pos>),
}

#[derive(TempRepr)]
enum NotationContextFrame<'a, Pos: Position> {
    DirectRev(TempRef<[NotationInfo<'a>]>),
    OpenSections(TempRef<[OpenSection<'a>]>),
    Parameterizations(TempRef<[WithSpan<Parameterization<'a, Pos>, Pos>]>),
    Parameterization(TempRef<Parameterization<'a, Pos>>),
    Mapping(TempRef<[MappingParam<'a, Pos>]>),
}

type NotationContext<'a, Pos> = TempStack<(), NotationContextFrame<'a, Pos>>;

#[derive(Clone, Copy)]
enum ParameterizationNotations<'a, 'b, Pos: Position> {
    DirectRev(&'b [NotationExpr<'a>]),
    Parameterizations(&'b TempStack<(), TempRef<[WithSpan<Parameterization<'a, Pos>, Pos>]>>),
    Mappings(&'b [Mapping<'a, Pos>]),
}

impl<'a, 'b, Pos: Position> ParameterizationNotations<'a, 'b, Pos> {
    fn for_each_notation_rev(&self, mut f: impl FnMut(Option<&NotationExpr<'a>>)) {
        match self {
            ParameterizationNotations::DirectRev(notations_rev) => {
                for notation in *notations_rev {
                    f(Some(notation));
                }
            }
            ParameterizationNotations::Parameterizations(parameterizations) => {
                for frame in parameterizations.iter() {
                    for parameterization in frame.iter().rev() {
                        ParameterIdentifier::for_each_param_notation_rev(
                            &parameterization.items,
                            |_, notation| f(Some(&notation.expr)),
                        );
                    }
                }
            }
            ParameterizationNotations::Mappings(mappings) => {
                for mapping in mappings.iter().rev() {
                    for param in mapping.params.iter().rev() {
                        f(param.notation.as_ref().map(|notation| &notation.expr));
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum RangeOverlap {
    Disjoint,
    Exact,
    Narrowing,
    Widening,
    Overlapping,
}

fn range_overlap(old_range: &Range<usize>, new_range: &Range<usize>) -> RangeOverlap {
    if new_range == old_range {
        RangeOverlap::Exact
    } else if new_range.start >= old_range.end || new_range.end <= old_range.start {
        RangeOverlap::Disjoint
    } else if new_range.start >= old_range.start && new_range.end <= old_range.end {
        RangeOverlap::Narrowing
    } else if new_range.start <= old_range.start && new_range.end >= old_range.end {
        RangeOverlap::Widening
    } else {
        RangeOverlap::Overlapping
    }
}

pub struct ParameterIdentifierConfig {
    metamodel_getter: &'static dyn MetaModelGetter,
    pub metamodel: Option<&'static dyn MetaModel>,
}

impl ParameterIdentifierConfig {
    pub fn new(metamodel_getter: &'static dyn MetaModelGetter) -> Self {
        ParameterIdentifierConfig {
            metamodel_getter,
            metamodel: None,
        }
    }
}

impl Clone for ParameterIdentifierConfig {
    fn clone(&self) -> Self {
        ParameterIdentifierConfig {
            metamodel_getter: self.metamodel_getter,
            metamodel: self.metamodel,
        }
    }
}

type Config = (
    (TokenizerConfig, ParenthesisMatcherConfig),
    ParameterIdentifierConfig,
);

impl CharParserDesc for ParameterIdentifierConfig {
    type Out<'a, Pos: Position> = ParameterEvent<'a, Pos>;
    type Config<'a> = Config;

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
    > = ComposedParser<
        IF,
        TokenEvent<'a>,
        ComposedParser<
            BufferedParserInterface<IF, TokenEvent<'a>>,
            Token<'a>,
            Tokenizer,
            ParenthesisMatcher,
        >,
        ParameterIdentifier<'a>,
    >;

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
        ComposedParser::new(
            ComposedParser::new(Tokenizer::new(), ParenthesisMatcher::new()),
            ParameterIdentifier::new(),
        )
    }
}

#[cfg(test)]
mod tests {
    use lang_def::parser::{str::StrPosition, DiagnosticSeverity::*, ErrorKind::*};
    use lang_test::parser::{ExpectedFragmentContent::*, *};

    use super::{
        super::metamodel::testing::TestMetaModel, IdentifierType::*, Token::*, TokenTree::*, *,
    };

    fn assert_parameter_identifier_output(
        expected_fragments: Vec<ExpectedFragment<ParameterEvent<StrPosition>>>,
    ) {
        assert_parser_output::<ParameterIdentifierConfig>(
            expected_fragments,
            (
                (TokenizerConfig, ParenthesisMatcherConfig),
                ParameterIdentifierConfig::new(&TestMetaModel),
            ),
        )
    }

    fn print_parameter_identifier_output(input: &str) {
        print_parser_output::<ParameterIdentifierConfig>(
            input,
            (
                (TokenizerConfig, ParenthesisMatcherConfig),
                ParameterIdentifierConfig::new(&TestMetaModel),
            ),
        )
    }

    #[test]
    fn metamodel() {
        assert_parameter_identifier_output(vec![(
            WithDiag(
                Box::new(Empty),
                (Error(Some(SyntaxError)), "expected keyword `%slate`".into()),
            ),
            None,
        )]);
        assert_parameter_identifier_output(vec![(
            WithDiag(
                Box::new(Input("x")),
                (Error(Some(SyntaxError)), "expected keyword `%slate`".into()),
            ),
            None,
        )]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (
                WithDiag(
                    Box::new(Empty),
                    (Error(Some(SyntaxError)), "expected metamodel name".into()),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDiag(
                    Box::new(Empty),
                    (Error(Some(SyntaxError)), "expected metamodel name".into()),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDiag(
                    Box::new(Input("x")),
                    (Error(Some(SyntaxError)), "expected string".into()),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Input("\"x\"")), SpanDesc::String)),
                    (
                        Error(Some(ResourceNotFound)),
                        "unknown metamodel \"x\"".into(),
                    ),
                ),
                None,
            ),
            (
                WithDiag(
                    Box::new(Empty),
                    (Error(Some(SyntaxError)), "expected `;`".into()),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Input("\"x\"")), SpanDesc::String)),
                    (
                        Error(Some(ResourceNotFound)),
                        "unknown metamodel \"x\"".into(),
                    ),
                ),
                None,
            ),
            (
                WithDiag(
                    Box::new(Empty),
                    (Error(Some(SyntaxError)), "expected `;`".into()),
                ),
                None,
            ),
            (Input(" x"), None),
        ]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Input("\"x\"")), SpanDesc::String)),
                    (
                        Error(Some(ResourceNotFound)),
                        "unknown metamodel \"x\"".into(),
                    ),
                ),
                None,
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDiag(
                    Box::new(WithDesc(Box::new(Input("\"x\"")), SpanDesc::String)),
                    (
                        Error(Some(ResourceNotFound)),
                        "unknown metamodel \"x\"".into(),
                    ),
                ),
                None,
            ),
            (Input(";"), None),
            (Input(" x;"), None),
        ]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("\"test\"")), SpanDesc::String),
                None,
            ),
            (
                WithDiag(
                    Box::new(Empty),
                    (Error(Some(SyntaxError)), "expected `;`".into()),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("\"test\"")), SpanDesc::String),
                None,
            ),
            (
                WithDiag(
                    Box::new(Empty),
                    (Error(Some(SyntaxError)), "expected `;`".into()),
                ),
                None,
            ),
            (Input(" "), None),
            (
                Input("x"),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: Vec::new(),
                        data: vec![WithSpan::new(
                            Token(Ident("x".into(), Unquoted)),
                            StrPosition::span_from_range(14..15),
                        )],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_output(vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("\"test\"")), SpanDesc::String),
                None,
            ),
            (Input(";"), None),
        ]);
    }

    #[test]
    fn globals() {
        print_parameter_identifier_output("%slate \"test\"; x;");
        print_parameter_identifier_output("%slate \"test\"; x : T;");
        print_parameter_identifier_output("%slate \"test\"; x : T := y;");
        print_parameter_identifier_output("%slate \"test\"; x %Type;");
        print_parameter_identifier_output("%slate \"test\"; x. T;");
        print_parameter_identifier_output("%slate \"test\"; x ⎿T⏌ := y;");
        print_parameter_identifier_output("%slate \"test\"; (x) : T := y;");
        print_parameter_identifier_output("%slate \"test\"; x ↦ y;");
        print_parameter_identifier_output("%slate \"test\"; (x : T) := y;");
        print_parameter_identifier_output("%slate \"test\"; x : T; y : U;");
        print_parameter_identifier_output("%slate \"test\"; x y : T;");
        print_parameter_identifier_output("%slate \"test\"; x^y_z : T;");
        print_parameter_identifier_output("%slate \"test\"; x y %z(a;b) : T;");
        print_parameter_identifier_output("%slate \"test\"; x() : T;");
        print_parameter_identifier_output("%slate \"test\"; x(,) : T;");
        print_parameter_identifier_output("%slate \"test\"; x(y,z) : T;");
        print_parameter_identifier_output("%slate \"test\"; x(y,z,) : T;");
        print_parameter_identifier_output("%slate \"test\"; x(,y,z,) : T;");
        print_parameter_identifier_output("%slate \"test\"; x(y,,z,) : T;");
        print_parameter_identifier_output("%slate \"test\"; x(y,z,,) : T;");
        print_parameter_identifier_output("%slate \"test\"; x(y;z) : T;");
        print_parameter_identifier_output("%slate \"test\"; x(42) : T;");
        print_parameter_identifier_output("%slate \"test\"; x,y : T;");
        print_parameter_identifier_output("%slate \"test\"; x,y, : T;");
        print_parameter_identifier_output("%slate \"test\"; x,,y : T;");
        print_parameter_identifier_output("%slate \"test\"; ,x : T;");
        print_parameter_identifier_output("%slate \"test\"; 42 : T;");
    }

    #[test]
    fn parameterizations() {
        print_parameter_identifier_output("%slate \"test\"; [b : B] a : A;");
        print_parameter_identifier_output("%slate \"test\"; [b : B] b : A;");
        print_parameter_identifier_output("%slate \"test\"; [b : B] a(b) : A;");
        print_parameter_identifier_output("%slate \"test\"; [b c : B] a(b c) : A;");
        print_parameter_identifier_output(
            "%slate \"test\"; [b, b c, c : B] c b a(b c, b, c, b b c, b c c) : A;",
        );
        print_parameter_identifier_output("%slate \"test\"; [b,c : B] b + c : A;");
        print_parameter_identifier_output("%slate \"test\"; [a b, b c : B] a b c : A;");
        print_parameter_identifier_output("%slate \"test\"; [[d : D] b,c : B] a : A;");
        print_parameter_identifier_output("%slate \"test\"; [[d : D] b : B; c : C] a : A;");
        print_parameter_identifier_output("%slate \"test\"; a := [b := c] b;");
        print_parameter_identifier_output("%slate \"test\"; a := [c := d] [b := c] b;");
        print_parameter_identifier_output("%slate \"test\"; a := [b, [d := e] [c := d] c, [f]];");
    }

    #[test]
    fn higher_order_parameterizations() {
        print_parameter_identifier_output("%slate \"test\"; [b : B] λ. b : A;");
        print_parameter_identifier_output("%slate \"test\"; [b : B] a(() ↦ b) : A;");
        print_parameter_identifier_output("%slate \"test\"; [[c : C] b(c) : B] λ c. b(c) : A;");
        print_parameter_identifier_output("%slate \"test\"; [[c : C] b(c) : B] λ c : C. b(c) : A;");
        print_parameter_identifier_output("%slate \"test\"; [[c : C] b(c) : B] λ d. b(d) : A;");
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C; d : D] b(c,d) : B] λ c,d. b(c,d) : A;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C; d : D] b(c,d) : B] λ c. λ d. b(c,d) : A;",
        );
        print_parameter_identifier_output(
            // Make sure that b(-2,-1) is not misidentified as b(c,d).
            "%slate \"test\"; [[c : C; d : D] b(c,d) : B; [d : D] e(d) : E] λ d. b(e(d),d) : A;",
        );
        print_parameter_identifier_output("%slate \"test\"; [[c : C] b(c) : B] a(c ↦ b(c)) : A;");
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C; d : D] b(c,d) : B] a((c,d) ↦ b(c,d)) : A;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C; d : D] b(c,d) : B] a(c ↦ d ↦ b(c,d)) : A;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C] { [d : D] b(c,d) : B; e(c) : E }] a(c ↦ (d ↦ b(c,d), e(c))) : A;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; [[d : D] b(d),c(d) : B] a(d ↦ b(d), d ↦ c(d)) : A;",
        );
        print_parameter_identifier_output("%slate \"test\"; [[c : C] b(c) : B] a(c ↦ b(x)) : A;");
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C] b(c) : B] a((c,d) ↦ b(c)) : A;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C] b(c) : B] a((c,d) ↦ b(d)) : A;",
        );
        print_parameter_identifier_output("%slate \"test\"; [[c : C] b(c) : B] a(d ↦ b(d)) : A;");
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C] b(c) : B] a(c ↦ b(c), d ↦ b(d)) : A;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; [[[e : E] d(e) : D] b(e ↦ d(e)),c(λ e. d(e)) : B] \
                              a((e ↦ d(e)) ↦ b(e ↦ d(e)), λ λ e. d(e). c(λ e. d(e))) : A;",
        );
    }

    #[test]
    fn sections() {
        print_parameter_identifier_output("%slate \"test\"; {}");
        print_parameter_identifier_output("%slate \"test\"; {};");
        print_parameter_identifier_output("%slate \"test\"; { x : T }");
        print_parameter_identifier_output("%slate \"test\"; { x : T; }");
        print_parameter_identifier_output("%slate \"test\"; { x : T; y : U; }");
        print_parameter_identifier_output("%slate \"test\"; { x : T; { y : U; } }");
        print_parameter_identifier_output(
            "%slate \"test\"; [a,b : T] { x_a : U; [c] y_a_b_c : V; } z_a : W;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; [[a : T] { b_a : U; }] { c(a ↦ b_a) : V; }",
        );
    }

    #[test]
    fn prefixes() {
        print_parameter_identifier_output("%slate \"test\"; x.{}");
        print_parameter_identifier_output("%slate \"test\"; x.y : T;");
        print_parameter_identifier_output("%slate \"test\"; x.y.{}");
        print_parameter_identifier_output("%slate \"test\"; x.{ y : T; }");
        print_parameter_identifier_output("%slate \"test\"; x.{ y.z : T; }");
        print_parameter_identifier_output("%slate \"test\"; (x y z).{}");
        print_parameter_identifier_output("%slate \"test\"; [x : T] x.{}");
        print_parameter_identifier_output("%slate \"test\"; [x y : T] (x y).{}");
        print_parameter_identifier_output("%slate \"test\"; [x : T] x.y : U;");
        print_parameter_identifier_output("%slate \"test\"; [x : T] x.(y) : U;");
        print_parameter_identifier_output("%slate \"test\"; [x : T] x.(y z) : U;");
        print_parameter_identifier_output("%slate \"test\"; [x,y : T] x.(y) : U;");
        print_parameter_identifier_output("%slate \"test\"; [x : T] x.y(z) : U;");
        print_parameter_identifier_output("%slate \"test\"; [x : T] x.y z : U;");
        print_parameter_identifier_output("%slate \"test\"; [x : T] x.y,z : U;");
    }

    #[test]
    fn objects() {
        print_parameter_identifier_output("%slate \"test\"; T := {};");
        print_parameter_identifier_output("%slate \"test\"; T := {x};");
        print_parameter_identifier_output("%slate \"test\"; T := {x || y};");
        print_parameter_identifier_output("%slate \"test\"; T := {x | | y};");
        print_parameter_identifier_output("%slate \"test\"; T := {x ||| y};");
        print_parameter_identifier_output("%slate \"test\"; T := {|x| || |y|};");
        print_parameter_identifier_output("%slate \"test\"; T := {x(y) | y : T |};");
        print_parameter_identifier_output("%slate \"test\"; T := {x(y) | y : T ||};");
        print_parameter_identifier_output("%slate \"test\"; T := {x(y) | y : T || z};");
        print_parameter_identifier_output("%slate \"test\"; T := {x(y) | y : T | a | b | c || z};");
        print_parameter_identifier_output("%slate \"test\"; T := {x(y) | y : T | z := λ a};");
        print_parameter_identifier_output(
            "%slate \"test\"; c := {x_i ↦ i | i : I || y_j_k ↦ j k | j : J; k : K | a | b} | {z};",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; ℕ := {0 || S(n) | n : ℕ}; \
                              [m,n : ℕ] m + n : ℕ := n.{0 ↦ m || S(x) ↦ S(m + x) | x : ℕ};",
        );
    }

    #[test]
    fn prefix_mappings() {
        print_parameter_identifier_output("%slate \"test\"; f := λ. x;");
        print_parameter_identifier_output("%slate \"test\"; f := λ a. x;");
        print_parameter_identifier_output("%slate \"test\"; f := λ a : A. x;");
        print_parameter_identifier_output("%slate \"test\"; f := (λ a. x, λ b. y);");
        print_parameter_identifier_output("%slate \"test\"; f := λ a,b. x;");
        print_parameter_identifier_output("%slate \"test\"; f := λ a,b,. x;");
        print_parameter_identifier_output("%slate \"test\"; f := λ a,,b. x;");
        print_parameter_identifier_output("%slate \"test\"; f := λ a : A, b : B. x;");
        print_parameter_identifier_output("%slate \"test\"; f := λ a;");
        print_parameter_identifier_output("%slate \"test\"; f := (λ a);");
        print_parameter_identifier_output(
            "%slate \"test\"; f := λ a : A, λ b : B. c_b : C, d : D. x;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; f := λ a : A, b : B ↦ c_b : C, d : D. x;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; a := f[λ b : B. b, λ λ d : D, e : E, f : E. c[d,f] : C. c[0,1]];",
        );
    }

    #[test]
    fn infix_mappings() {
        print_parameter_identifier_output("%slate \"test\"; f := (() ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := (a ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := (a : A ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := ((a) ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := ((a : A) ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := (a(b) ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := (a, b ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := (a ↦ x, b ↦ y);");
        print_parameter_identifier_output("%slate \"test\"; f := ((a,b) ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := ((a,b,) ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := ((a,,b) ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := ((a : A, b : B) ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := (a ↦ b ↦ x);");
        print_parameter_identifier_output("%slate \"test\"; f := ((a ↦ b) ↦ x);");
        print_parameter_identifier_output(
            "%slate \"test\"; f := ((a : A, b : B ↦ c_b : C, d : D) ↦ x);",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; f := ((a : A, λ b : B. c_b : C, d : D) ↦ x);",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; a := f[(b : B) ↦ b, ((d : D, e : E, f : E) ↦ c[d,f] : C) ↦ c[0,1]];",
        );
    }

    #[test]
    fn range_overlaps() {
        assert_eq!(range_overlap(&(0..0), &(0..0)), RangeOverlap::Exact);
        assert_eq!(range_overlap(&(0..1), &(0..1)), RangeOverlap::Exact);
        assert_eq!(range_overlap(&(0..0), &(0..1)), RangeOverlap::Disjoint);
        assert_eq!(range_overlap(&(0..1), &(0..0)), RangeOverlap::Disjoint);
        assert_eq!(range_overlap(&(0..1), &(1..1)), RangeOverlap::Disjoint);
        assert_eq!(range_overlap(&(1..1), &(0..1)), RangeOverlap::Disjoint);
        assert_eq!(range_overlap(&(0..1), &(1..2)), RangeOverlap::Disjoint);
        assert_eq!(range_overlap(&(1..2), &(0..1)), RangeOverlap::Disjoint);
        assert_eq!(range_overlap(&(0..1), &(2..3)), RangeOverlap::Disjoint);
        assert_eq!(range_overlap(&(2..3), &(0..1)), RangeOverlap::Disjoint);
        assert_eq!(range_overlap(&(0..2), &(0..1)), RangeOverlap::Narrowing);
        assert_eq!(range_overlap(&(0..2), &(1..2)), RangeOverlap::Narrowing);
        assert_eq!(range_overlap(&(0..3), &(1..2)), RangeOverlap::Narrowing);
        assert_eq!(range_overlap(&(0..1), &(0..2)), RangeOverlap::Widening);
        assert_eq!(range_overlap(&(1..2), &(0..2)), RangeOverlap::Widening);
        assert_eq!(range_overlap(&(1..2), &(0..3)), RangeOverlap::Widening);
        assert_eq!(range_overlap(&(0..2), &(1..3)), RangeOverlap::Overlapping);
        assert_eq!(range_overlap(&(1..3), &(0..2)), RangeOverlap::Overlapping);
    }
}
