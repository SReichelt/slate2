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
    pub data: Option<T>, // `None` in case of some syntax errors
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

// TODO: make prefix spans more specific
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
    use lang_def::parser::{str::StrPosition, DiagnosticSeverity::*, ErrorKind::*, WarningKind::*};
    use lang_test::parser::{ExpectedFragmentContent::*, *};

    use super::{
        super::metamodel::testing::{TestInfixMapping, TestMetaModel, TestPrefixMapping},
        IdentifierType::*,
        Token::*,
        TokenIsolation::*,
        TokenTree::*,
        *,
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

    fn assert_parameter_identifier_test_output(
        expected_fragments: Vec<ExpectedFragment<ParameterEvent<StrPosition>>>,
    ) {
        let mut expected_test_fragments = vec![
            (WithDesc(Box::new(Input("%slate")), SpanDesc::Keyword), None),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("\"test\"")), SpanDesc::String),
                None,
            ),
            (Input("; "), None),
        ];
        expected_test_fragments.extend(expected_fragments);
        assert_parameter_identifier_output(expected_test_fragments);
    }

    #[allow(dead_code)]
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
        assert_parameter_identifier_test_output(vec![
            (
                Input("x"),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: Vec::new(),
                        data: vec![WithSpan::new(
                            Token(Ident("x".into(), Unquoted)),
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(18),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T := y"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(18),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(23),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::from_usize(24)..StrPosition::from_usize(25),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Type)),
                    ),
                    Input(" "),
                    WithDesc(Box::new(Input("%Type")), SpanDesc::Keyword),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Type),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![WithSpan::new(
                            Token(Keyword("%Type".into())),
                            StrPosition::from_usize(17)..StrPosition::from_usize(22),
                        )],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (Input("x. "), None),
            (
                Input("T"),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Ident("x".into()),
                        StrPosition::from_usize(15)..StrPosition::from_usize(16),
                    )],
                    data: Some(ParamGroup {
                        param_notations: Vec::new(),
                        data: vec![WithSpan::new(
                            Token(Ident("T".into(), Unquoted)),
                            StrPosition::from_usize(18)..StrPosition::from_usize(19),
                        )],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" "),
                    WithDesc(Box::new(Input("⎿")), SpanDesc::ParenStart),
                    Input("T"),
                    WithDesc(Box::new(Input("⏌")), SpanDesc::ParenEnd),
                    Input(" := y"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Paren(
                                    '⎿',
                                    vec![WithSpan::new(
                                        Token(Ident("T".into(), Unquoted)),
                                        StrPosition::from_usize(20)..StrPosition::from_usize(21),
                                    )],
                                ),
                                StrPosition::from_usize(17)..StrPosition::from_usize(24),
                            ),
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(25)..StrPosition::from_usize(27),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::from_usize(28)..StrPosition::from_usize(29),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("x"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T := y"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Paren(
                                    '(',
                                    vec![vec![NotationExpr::Ident("x".into())]],
                                ),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(23)..StrPosition::from_usize(25),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::from_usize(26)..StrPosition::from_usize(27),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" ↦ y"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident("↦".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("x : T"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := y"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Paren(
                                    '(',
                                    vec![vec![NotationExpr::Seq(vec![
                                        NotationExpr::Ident("x".into()),
                                        NotationExpr::Ident(":".into()),
                                        NotationExpr::Ident("T".into()),
                                    ])]],
                                ),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(22),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(23)..StrPosition::from_usize(25),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::from_usize(26)..StrPosition::from_usize(27),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(18),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("y".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(22)..StrPosition::from_usize(23),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(24)..StrPosition::from_usize(25),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(26)..StrPosition::from_usize(27),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Ident("y".into()),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x^y_z")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::ReservedChar('^'),
                                    NotationExpr::Ident("y".into()),
                                    NotationExpr::ReservedChar('_'),
                                    NotationExpr::Ident("z".into()),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(20),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(23)..StrPosition::from_usize(24),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    Input("x y "),
                    WithDesc(Box::new(Input("%z")), SpanDesc::Keyword),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    Input("a;b"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: Vec::new(),
                        data: vec![
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(15)..StrPosition::from_usize(16),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(18),
                            ),
                            WithSpan::new(
                                Token(Keyword("%z".into())),
                                StrPosition::from_usize(19)..StrPosition::from_usize(21),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Token(Ident("a".into(), Unquoted)),
                                            StrPosition::from_usize(22)
                                                ..StrPosition::from_usize(23),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(
                                                ';',
                                                StronglyConnected,
                                                StronglyConnected,
                                            )),
                                            StrPosition::from_usize(23)
                                                ..StrPosition::from_usize(24),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("b".into(), Unquoted)),
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(25),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(21)..StrPosition::from_usize(26),
                            ),
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(27)..StrPosition::from_usize(28),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Paren('(', Vec::new()),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDiag(
                                Box::new(Input(",")),
                                (Error(Some(SyntaxError)), "superfluous comma".into()),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Paren('(', Vec::new()),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(19),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(20)..StrPosition::from_usize(21),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(22)..StrPosition::from_usize(23),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("y,z"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Ident("y".into()),
                                            NotationExpr::Ident("z".into()),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(21),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(22)..StrPosition::from_usize(23),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(24)..StrPosition::from_usize(25),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("y,z,"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Ident("y".into()),
                                            NotationExpr::Ident("z".into()),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(22),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(23)..StrPosition::from_usize(24),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(25)..StrPosition::from_usize(26),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDiag(
                                Box::new(Input(",")),
                                (Error(Some(SyntaxError)), "superfluous comma".into()),
                            ),
                            Input("y,z,"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Ident("y".into()),
                                            NotationExpr::Ident("z".into()),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(23),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(24)..StrPosition::from_usize(25),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(26)..StrPosition::from_usize(27),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("y,"),
                            WithDiag(
                                Box::new(Input(",")),
                                (Error(Some(SyntaxError)), "superfluous comma".into()),
                            ),
                            Input("z,"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Ident("y".into()),
                                            NotationExpr::Ident("z".into()),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(23),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(24)..StrPosition::from_usize(25),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(26)..StrPosition::from_usize(27),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("y,z,"),
                            WithDiag(
                                Box::new(Input(",")),
                                (Error(Some(SyntaxError)), "superfluous comma".into()),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Ident("y".into()),
                                            NotationExpr::Ident("z".into()),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(23),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(24)..StrPosition::from_usize(25),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(26)..StrPosition::from_usize(27),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("y;z"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![
                                            vec![NotationExpr::Ident("y".into())],
                                            vec![NotationExpr::Ident("z".into())],
                                        ],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(21),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(22)..StrPosition::from_usize(23),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(24)..StrPosition::from_usize(25),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(Box::new(Input("42")), SpanDesc::Number),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Ident("42".into())]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(20),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(23)..StrPosition::from_usize(24),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("x".into()),
                                    scope: NameScopeDesc::Global,
                                    kind: None,
                                },
                                StrPosition::from_usize(15)..StrPosition::from_usize(16),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("y".into()),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::from_usize(17)..StrPosition::from_usize(18),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(", "),
                    WithDiag(
                        Box::new(Empty),
                        (Error(Some(SyntaxError)), "expected name/notation".into()),
                    ),
                    Input(": T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("x".into()),
                                    scope: NameScopeDesc::Global,
                                    kind: None,
                                },
                                StrPosition::from_usize(15)..StrPosition::from_usize(16),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("y".into()),
                                    scope: NameScopeDesc::Global,
                                    kind: None,
                                },
                                StrPosition::from_usize(17)..StrPosition::from_usize(18),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(20)..StrPosition::from_usize(21),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(22)..StrPosition::from_usize(23),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(","),
                    WithDiag(
                        Box::new(Empty),
                        (Error(Some(SyntaxError)), "expected name/notation".into()),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("x".into()),
                                    scope: NameScopeDesc::Global,
                                    kind: None,
                                },
                                StrPosition::from_usize(15)..StrPosition::from_usize(16),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("y".into()),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::from_usize(18)..StrPosition::from_usize(19),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(20)..StrPosition::from_usize(21),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(22)..StrPosition::from_usize(23),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                WithDiag(
                    Box::new(Empty),
                    (Error(Some(SyntaxError)), "expected name/notation".into()),
                ),
                None,
            ),
            (
                Seq(vec![
                    Input(","),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(16)..StrPosition::from_usize(17),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(18)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(20)..StrPosition::from_usize(21),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(WithDesc(
                            Box::new(Input("42")),
                            SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                        )),
                        SpanDesc::Number,
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("42".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(17),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(18)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(20)..StrPosition::from_usize(21),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
    }

    #[test]
    fn parameterizations() {
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("b".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("a".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(23)..StrPosition::from_usize(24),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(25)..StrPosition::from_usize(26),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(27)..StrPosition::from_usize(28),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDiag(
                        Box::new(WithDesc(
                            Box::new(WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            )),
                            SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                        )),
                        (
                            Error(Some(SyntaxError)),
                            "a notation cannot consist entirely of a parameter".into(),
                        ),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("b".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: Vec::new(),
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(25)..StrPosition::from_usize(26),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(27)..StrPosition::from_usize(28),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("b".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(23)..StrPosition::from_usize(27),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(28)..StrPosition::from_usize(29),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(30)..StrPosition::from_usize(31),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("b c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Seq(vec![
                                                NotationExpr::Ident("b".into()),
                                                NotationExpr::Ident("c".into()),
                                            ]),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(19),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(22)
                                                ..StrPosition::from_usize(23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(24),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(25)..StrPosition::from_usize(31),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(32)..StrPosition::from_usize(33),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(34)..StrPosition::from_usize(35),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(", "),
                    WithDesc(
                        Box::new(Input("b c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(", "),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(" "),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(" a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("b c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(" "),
                            WithDesc(
                                Box::new(Input("b c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Input("b c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(" "),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("b".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(16)
                                                ..StrPosition::from_usize(17),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Seq(vec![
                                                    NotationExpr::Ident("b".into()),
                                                    NotationExpr::Ident("c".into()),
                                                ]),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(22),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("c".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(25),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(26)
                                                ..StrPosition::from_usize(27),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(28)
                                                ..StrPosition::from_usize(29),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Param(-1),
                                    NotationExpr::Param(-3),
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Param(-2),
                                            NotationExpr::Param(-3),
                                            NotationExpr::Param(-1),
                                            NotationExpr::Seq(vec![
                                                NotationExpr::Param(-3),
                                                NotationExpr::Param(-2),
                                            ]),
                                            NotationExpr::Seq(vec![
                                                NotationExpr::Param(-2),
                                                NotationExpr::Param(-1),
                                            ]),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(31)..StrPosition::from_usize(61),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(62)..StrPosition::from_usize(63),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(64)..StrPosition::from_usize(65),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(" + "),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("b".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(16)
                                                ..StrPosition::from_usize(17),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("c".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(22)
                                                ..StrPosition::from_usize(23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(24),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Param(-2),
                                    NotationExpr::Ident("+".into()),
                                    NotationExpr::Param(-1),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(25)..StrPosition::from_usize(30),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(33)..StrPosition::from_usize(34),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(", "),
                    WithDesc(
                        Box::new(Input("b c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDiag(
                        Box::new(WithDesc(
                            Box::new(Input("a b c")),
                            SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                        )),
                        (
                            Error(Some(SyntaxError)),
                            "ambiguous parameter references in notation".into(),
                        ),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Seq(vec![
                                                    NotationExpr::Ident("a".into()),
                                                    NotationExpr::Ident("b".into()),
                                                ]),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(16)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Seq(vec![
                                                    NotationExpr::Ident("b".into()),
                                                    NotationExpr::Ident("c".into()),
                                                ]),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(24),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(25)
                                                ..StrPosition::from_usize(26),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(27)
                                                ..StrPosition::from_usize(28),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(29),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Ident("c".into()),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(30)..StrPosition::from_usize(35),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(36)..StrPosition::from_usize(37),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(38)..StrPosition::from_usize(39),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: vec![WithSpan::new(
                                    super::Parameterization {
                                        kind: &TestMetaModel,
                                        items: vec![Parameterized {
                                            parameterizations: Vec::new(),
                                            prefixes: Vec::new(),
                                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                                param_notations: vec![WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("d".into()),
                                                        scope: NameScopeDesc::Param,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::from_usize(17)
                                                        ..StrPosition::from_usize(18),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::from_usize(19)
                                                            ..StrPosition::from_usize(20),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("D".into(), Unquoted)),
                                                        StrPosition::from_usize(21)
                                                            ..StrPosition::from_usize(22),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    StrPosition::from_usize(16)..StrPosition::from_usize(23),
                                )],
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("b".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(25),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("c".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Function),
                                            },
                                            StrPosition::from_usize(26)
                                                ..StrPosition::from_usize(27),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(28)
                                                ..StrPosition::from_usize(29),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(30)
                                                ..StrPosition::from_usize(31),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(32),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("a".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(33)..StrPosition::from_usize(34),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(35)..StrPosition::from_usize(36),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(37)..StrPosition::from_usize(38),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B; "),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![
                                Parameterized {
                                    parameterizations: vec![WithSpan::new(
                                        super::Parameterization {
                                            kind: &TestMetaModel,
                                            items: vec![Parameterized {
                                                parameterizations: Vec::new(),
                                                prefixes: Vec::new(),
                                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                                    param_notations: vec![WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("d".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::from_usize(17)
                                                            ..StrPosition::from_usize(18),
                                                    )],
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::from_usize(19)
                                                                ..StrPosition::from_usize(20),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("D".into(), Unquoted)),
                                                            StrPosition::from_usize(21)
                                                                ..StrPosition::from_usize(22),
                                                        ),
                                                    ],
                                                })),
                                            }],
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                                    )],
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("b".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Function),
                                            },
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(26)
                                                    ..StrPosition::from_usize(27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("B".into(), Unquoted)),
                                                StrPosition::from_usize(28)
                                                    ..StrPosition::from_usize(29),
                                            ),
                                        ],
                                    })),
                                },
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("c".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(31)
                                                ..StrPosition::from_usize(32),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(33)
                                                    ..StrPosition::from_usize(34),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::from_usize(35)
                                                    ..StrPosition::from_usize(36),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(37),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("a".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(38)..StrPosition::from_usize(39),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(40)..StrPosition::from_usize(41),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(42)..StrPosition::from_usize(43),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Local, None),
                    ),
                    Input(" := c"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" b"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("a".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Parameterization(super::Parameterization {
                                    kind: &TestMetaModel,
                                    items: vec![Parameterized {
                                        parameterizations: Vec::new(),
                                        prefixes: Vec::new(),
                                        data: Some(SectionItem::ParamGroup(ParamGroup {
                                            param_notations: vec![WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("b".into()),
                                                    scope: NameScopeDesc::Local,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(22),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":=".into(), Unquoted)),
                                                    StrPosition::from_usize(23)
                                                        ..StrPosition::from_usize(25),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("c".into(), Unquoted)),
                                                    StrPosition::from_usize(26)
                                                        ..StrPosition::from_usize(27),
                                                ),
                                            ],
                                        })),
                                    }],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(28),
                            ),
                            WithSpan::new(
                                Token(Ident("b".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Local, None),
                    ),
                    Input(" := d"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Local, None),
                    ),
                    Input(" := c"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" b"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("a".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Parameterization(super::Parameterization {
                                    kind: &TestMetaModel,
                                    items: vec![Parameterized {
                                        parameterizations: Vec::new(),
                                        prefixes: Vec::new(),
                                        data: Some(SectionItem::ParamGroup(ParamGroup {
                                            param_notations: vec![WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("c".into()),
                                                    scope: NameScopeDesc::Local,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(22),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":=".into(), Unquoted)),
                                                    StrPosition::from_usize(23)
                                                        ..StrPosition::from_usize(25),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("d".into(), Unquoted)),
                                                    StrPosition::from_usize(26)
                                                        ..StrPosition::from_usize(27),
                                                ),
                                            ],
                                        })),
                                    }],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(28),
                            ),
                            WithSpan::new(
                                Parameterization(super::Parameterization {
                                    kind: &TestMetaModel,
                                    items: vec![Parameterized {
                                        parameterizations: Vec::new(),
                                        prefixes: Vec::new(),
                                        data: Some(SectionItem::ParamGroup(ParamGroup {
                                            param_notations: vec![WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("b".into()),
                                                    scope: NameScopeDesc::Local,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(30)
                                                    ..StrPosition::from_usize(31),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":=".into(), Unquoted)),
                                                    StrPosition::from_usize(32)
                                                        ..StrPosition::from_usize(34),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("c".into(), Unquoted)),
                                                    StrPosition::from_usize(35)
                                                        ..StrPosition::from_usize(36),
                                                ),
                                            ],
                                        })),
                                    }],
                                }),
                                StrPosition::from_usize(29)..StrPosition::from_usize(37),
                            ),
                            WithSpan::new(
                                Token(Ident("b".into(), Unquoted)),
                                StrPosition::from_usize(38)..StrPosition::from_usize(39),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    Input("b, "),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Local, None),
                    ),
                    Input(" := e"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Local, None),
                    ),
                    Input(" := d"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" c, "),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    Input("f"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("a".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '[',
                                    vec![
                                        WithSpan::new(
                                            Token(Ident("b".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::from_usize(22)
                                                ..StrPosition::from_usize(23),
                                        ),
                                        WithSpan::new(
                                            Parameterization(super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: vec![Parameterized {
                                                    parameterizations: Vec::new(),
                                                    prefixes: Vec::new(),
                                                    data: Some(SectionItem::ParamGroup(
                                                        ParamGroup {
                                                            param_notations: vec![WithSpan::new(
                                                                Notation {
                                                                    expr: NotationExpr::Ident(
                                                                        "d".into(),
                                                                    ),
                                                                    scope: NameScopeDesc::Local,
                                                                    kind: None,
                                                                },
                                                                StrPosition::from_usize(25)
                                                                    ..StrPosition::from_usize(26),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":=".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(27)
                                                                        ..StrPosition::from_usize(
                                                                            29,
                                                                        ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "e".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(30)
                                                                        ..StrPosition::from_usize(
                                                                            31,
                                                                        ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            }),
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(32),
                                        ),
                                        WithSpan::new(
                                            Parameterization(super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: vec![Parameterized {
                                                    parameterizations: Vec::new(),
                                                    prefixes: Vec::new(),
                                                    data: Some(SectionItem::ParamGroup(
                                                        ParamGroup {
                                                            param_notations: vec![WithSpan::new(
                                                                Notation {
                                                                    expr: NotationExpr::Ident(
                                                                        "c".into(),
                                                                    ),
                                                                    scope: NameScopeDesc::Local,
                                                                    kind: None,
                                                                },
                                                                StrPosition::from_usize(34)
                                                                    ..StrPosition::from_usize(35),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":=".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(36)
                                                                        ..StrPosition::from_usize(
                                                                            38,
                                                                        ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "d".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(39)
                                                                        ..StrPosition::from_usize(
                                                                            40,
                                                                        ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            }),
                                            StrPosition::from_usize(33)
                                                ..StrPosition::from_usize(41),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("c".into(), Unquoted)),
                                            StrPosition::from_usize(42)
                                                ..StrPosition::from_usize(43),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::from_usize(43)
                                                ..StrPosition::from_usize(44),
                                        ),
                                        WithSpan::new(
                                            Paren(
                                                '[',
                                                vec![WithSpan::new(
                                                    Token(Ident("f".into(), Unquoted)),
                                                    StrPosition::from_usize(46)
                                                        ..StrPosition::from_usize(47),
                                                )],
                                            ),
                                            StrPosition::from_usize(45)
                                                ..StrPosition::from_usize(48),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(49),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
    }

    #[test]
    fn higher_order_parameterizations() {
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("b".into()),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(16)..StrPosition::from_usize(17),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(18)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(20)..StrPosition::from_usize(21),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(22),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("λ. "),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params_len: 0,
                                    target_expr: NotationExpr::Param(-1),
                                })),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(23)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("b".into()),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(16)..StrPosition::from_usize(17),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(18)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(20)..StrPosition::from_usize(21),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(22),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Mapping(Box::new(
                                            MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 0,
                                                target_expr: NotationExpr::Param(-1),
                                            },
                                        ))]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(23)..StrPosition::from_usize(34),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(35)..StrPosition::from_usize(36),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(37)..StrPosition::from_usize(38),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(33),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("λ "),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(". "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params_len: 1,
                                    target_expr: NotationExpr::Param(-2),
                                })),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(34)..StrPosition::from_usize(44),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(45)..StrPosition::from_usize(46),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(47)..StrPosition::from_usize(48),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(33),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("λ "),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(" "),
                            WithDiag(
                                Box::new(Input(": C")),
                                (
                                    Error(Some(SyntaxError)),
                                    "a mapping parameter within a notation cannot be followed by \
                                     additional data"
                                        .into(),
                                ),
                            ),
                            Input(". "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(
                                            NameScopeDesc::Param,
                                            Some(NameKindDesc::Value),
                                        ),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params_len: 1,
                                    target_expr: NotationExpr::Param(-2),
                                })),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(34)..StrPosition::from_usize(48),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(49)..StrPosition::from_usize(50),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(51)..StrPosition::from_usize(52),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(33),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("λ "),
                            WithDiag(
                                Box::new(WithDesc(
                                    Box::new(Input("d")),
                                    SpanDesc::NameDef(NameScopeDesc::Param, None),
                                )),
                                (
                                    Warning(Some(SyntaxWarning)),
                                    "mapping parameter name does not match parameterization; \
                                     expected `c`"
                                        .into(),
                                ),
                            ),
                            Input(". "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params_len: 1,
                                    target_expr: NotationExpr::Param(-2),
                                })),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(34)..StrPosition::from_usize(44),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(45)..StrPosition::from_usize(46),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(47)..StrPosition::from_usize(48),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("c".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(17)
                                                ..StrPosition::from_usize(18),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(19)
                                                    ..StrPosition::from_usize(20),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(22),
                                            ),
                                        ],
                                    })),
                                },
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("d".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(26)
                                                    ..StrPosition::from_usize(27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::from_usize(28)
                                                    ..StrPosition::from_usize(29),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Param(-2),
                                            NotationExpr::Param(-1),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(31)..StrPosition::from_usize(37),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(38)..StrPosition::from_usize(39),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(40)..StrPosition::from_usize(41),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(42),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C; "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("λ "),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(". "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    Input(","),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params_len: 2,
                                    target_expr: NotationExpr::Param(-3),
                                })),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(43)..StrPosition::from_usize(57),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(58)..StrPosition::from_usize(59),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(60)..StrPosition::from_usize(61),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("c".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(17)
                                                ..StrPosition::from_usize(18),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(19)
                                                    ..StrPosition::from_usize(20),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(22),
                                            ),
                                        ],
                                    })),
                                },
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("d".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(26)
                                                    ..StrPosition::from_usize(27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::from_usize(28)
                                                    ..StrPosition::from_usize(29),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Param(-2),
                                            NotationExpr::Param(-1),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(31)..StrPosition::from_usize(37),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(38)..StrPosition::from_usize(39),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(40)..StrPosition::from_usize(41),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(42),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C; "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("λ "),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(". λ "),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(". "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    Input(","),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params_len: 1,
                                    target_expr: NotationExpr::Mapping(Box::new(
                                        MappingNotationExpr {
                                            kind: &TestPrefixMapping,
                                            params_len: 1,
                                            target_expr: NotationExpr::Param(-3),
                                        },
                                    )),
                                })),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(43)..StrPosition::from_usize(61),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(62)..StrPosition::from_usize(63),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(64)..StrPosition::from_usize(65),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let diag_fragment = WithDiag(
            Box::new(Seq(vec![
                Input("b"),
                WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                WithDesc(
                    Box::new(Seq(vec![
                        Input("e"),
                        WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                        WithDesc(
                            Box::new(Input("d")),
                            SpanDesc::NameRef(NameScopeDesc::Param, None),
                        ),
                        WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    ])),
                    SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                ),
                Input(","),
                WithDesc(
                    Box::new(Input("d")),
                    SpanDesc::NameRef(NameScopeDesc::Param, None),
                ),
                WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
            ])),
            (
                Error(Some(SyntaxError)),
                "a mapping target within a notation cannot reference a \
                 standalone mapping parameter"
                    .into(),
            ),
        );
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![
                    Parameterized {
                        parameterizations: vec![WithSpan::new(
                            super::Parameterization {
                                kind: &TestMetaModel,
                                items: vec![
                                    Parameterized {
                                        parameterizations: Vec::new(),
                                        prefixes: Vec::new(),
                                        data: Some(SectionItem::ParamGroup(ParamGroup {
                                            param_notations: vec![WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("c".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::from_usize(17)
                                                    ..StrPosition::from_usize(18),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(19)
                                                        ..StrPosition::from_usize(20),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("C".into(), Unquoted)),
                                                    StrPosition::from_usize(21)
                                                        ..StrPosition::from_usize(22),
                                                ),
                                            ],
                                        })),
                                    },
                                    Parameterized {
                                        parameterizations: Vec::new(),
                                        prefixes: Vec::new(),
                                        data: Some(SectionItem::ParamGroup(ParamGroup {
                                            param_notations: vec![WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("d".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::from_usize(24)
                                                    ..StrPosition::from_usize(25),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(26)
                                                        ..StrPosition::from_usize(27),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("D".into(), Unquoted)),
                                                    StrPosition::from_usize(28)
                                                        ..StrPosition::from_usize(29),
                                                ),
                                            ],
                                        })),
                                    },
                                ],
                            },
                            StrPosition::from_usize(16)..StrPosition::from_usize(30),
                        )],
                        prefixes: Vec::new(),
                        data: Some(SectionItem::ParamGroup(ParamGroup {
                            param_notations: vec![WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Seq(vec![
                                        NotationExpr::Ident("b".into()),
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                NotationExpr::Param(-2),
                                                NotationExpr::Param(-1),
                                            ]],
                                        ),
                                    ]),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::from_usize(31)..StrPosition::from_usize(37),
                            )],
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::from_usize(38)..StrPosition::from_usize(39),
                                ),
                                WithSpan::new(
                                    Token(Ident("B".into(), Unquoted)),
                                    StrPosition::from_usize(40)..StrPosition::from_usize(41),
                                ),
                            ],
                        })),
                    },
                    Parameterized {
                        parameterizations: vec![WithSpan::new(
                            super::Parameterization {
                                kind: &TestMetaModel,
                                items: vec![Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("d".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(44)
                                                ..StrPosition::from_usize(45),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(46)
                                                    ..StrPosition::from_usize(47),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::from_usize(48)
                                                    ..StrPosition::from_usize(49),
                                            ),
                                        ],
                                    })),
                                }],
                            },
                            StrPosition::from_usize(43)..StrPosition::from_usize(50),
                        )],
                        prefixes: Vec::new(),
                        data: Some(SectionItem::ParamGroup(ParamGroup {
                            param_notations: vec![WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Seq(vec![
                                        NotationExpr::Ident("e".into()),
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![NotationExpr::Param(-1)]],
                                        ),
                                    ]),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::from_usize(51)..StrPosition::from_usize(55),
                            )],
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::from_usize(56)..StrPosition::from_usize(57),
                                ),
                                WithSpan::new(
                                    Token(Ident("E".into(), Unquoted)),
                                    StrPosition::from_usize(58)..StrPosition::from_usize(59),
                                ),
                            ],
                        })),
                    },
                ],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(60),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C; "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B; "),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("e"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : E"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("λ "),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(". "),
                            diag_fragment,
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params_len: 1,
                                    // Make sure that b(-2,-1) is not misidentified as b(c,d).
                                    target_expr: NotationExpr::Seq(vec![
                                        NotationExpr::Ident("b".into()),
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                NotationExpr::Param(-2),
                                                NotationExpr::Param(-1),
                                            ]],
                                        ),
                                    ]),
                                })),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(61)..StrPosition::from_usize(76),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(77)..StrPosition::from_usize(78),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(79)..StrPosition::from_usize(80),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(33),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Mapping(Box::new(
                                            MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Param(-2),
                                            },
                                        ))]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(34)..StrPosition::from_usize(47),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(48)..StrPosition::from_usize(49),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(50)..StrPosition::from_usize(51),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("c".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(17)
                                                ..StrPosition::from_usize(18),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(19)
                                                    ..StrPosition::from_usize(20),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(22),
                                            ),
                                        ],
                                    })),
                                },
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("d".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(26)
                                                    ..StrPosition::from_usize(27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::from_usize(28)
                                                    ..StrPosition::from_usize(29),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Param(-2),
                                            NotationExpr::Param(-1),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(31)..StrPosition::from_usize(37),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(38)..StrPosition::from_usize(39),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(40)..StrPosition::from_usize(41),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(42),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C; "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    Input(","),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Mapping(Box::new(
                                            MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 2,
                                                target_expr: NotationExpr::Param(-3),
                                            },
                                        ))]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(43)..StrPosition::from_usize(62),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(63)..StrPosition::from_usize(64),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(65)..StrPosition::from_usize(66),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("c".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(17)
                                                ..StrPosition::from_usize(18),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(19)
                                                    ..StrPosition::from_usize(20),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(22),
                                            ),
                                        ],
                                    })),
                                },
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("d".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(26)
                                                    ..StrPosition::from_usize(27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::from_usize(28)
                                                    ..StrPosition::from_usize(29),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Param(-2),
                                            NotationExpr::Param(-1),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(31)..StrPosition::from_usize(37),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(38)..StrPosition::from_usize(39),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(40)..StrPosition::from_usize(41),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(42),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C; "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    Input(","),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Mapping(Box::new(
                                            MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Mapping(Box::new(
                                                    MappingNotationExpr {
                                                        kind: &TestInfixMapping,
                                                        params_len: 1,
                                                        target_expr: NotationExpr::Param(-3),
                                                    },
                                                )),
                                            },
                                        ))]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(43)..StrPosition::from_usize(64),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(65)..StrPosition::from_usize(66),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(67)..StrPosition::from_usize(68),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::Section(Section {
                        kind: &TestMetaModel,
                        items: vec![
                            Parameterized {
                                parameterizations: vec![WithSpan::new(
                                    super::Parameterization {
                                        kind: &TestMetaModel,
                                        items: vec![Parameterized {
                                            parameterizations: Vec::new(),
                                            prefixes: Vec::new(),
                                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                                param_notations: vec![WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("d".into()),
                                                        scope: NameScopeDesc::Param,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::from_usize(27)
                                                        ..StrPosition::from_usize(28),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::from_usize(29)
                                                            ..StrPosition::from_usize(30),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("D".into(), Unquoted)),
                                                        StrPosition::from_usize(31)
                                                            ..StrPosition::from_usize(32),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    StrPosition::from_usize(26)..StrPosition::from_usize(33),
                                )],
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Seq(vec![
                                                NotationExpr::Ident("b".into()),
                                                NotationExpr::Paren(
                                                    '(',
                                                    vec![vec![
                                                        NotationExpr::Param(-2),
                                                        NotationExpr::Param(-1),
                                                    ]],
                                                ),
                                            ]),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Function),
                                        },
                                        StrPosition::from_usize(34)..StrPosition::from_usize(40),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(41)
                                                ..StrPosition::from_usize(42),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(43)
                                                ..StrPosition::from_usize(44),
                                        ),
                                    ],
                                })),
                            },
                            Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Seq(vec![
                                                NotationExpr::Ident("e".into()),
                                                NotationExpr::Paren(
                                                    '(',
                                                    vec![vec![NotationExpr::Param(-1)]],
                                                ),
                                            ]),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Function),
                                        },
                                        StrPosition::from_usize(46)..StrPosition::from_usize(50),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(51)
                                                ..StrPosition::from_usize(52),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::from_usize(53)
                                                ..StrPosition::from_usize(54),
                                        ),
                                    ],
                                })),
                            },
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(58),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    Input(" "),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B; "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("e"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : E; "),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    Input(","),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("e"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Mapping(Box::new(
                                            MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Paren(
                                                    '(',
                                                    vec![vec![
                                                        NotationExpr::Mapping(Box::new(
                                                            MappingNotationExpr {
                                                                kind: &TestInfixMapping,
                                                                params_len: 1,
                                                                target_expr: NotationExpr::Param(
                                                                    -4,
                                                                ),
                                                            },
                                                        )),
                                                        NotationExpr::Param(-2),
                                                    ]],
                                                ),
                                            },
                                        ))]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(59)..StrPosition::from_usize(88),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(89)..StrPosition::from_usize(90),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(91)..StrPosition::from_usize(92),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("d".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("D".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Seq(vec![
                                        NotationExpr::Ident("b".into()),
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![NotationExpr::Param(-1)]],
                                        ),
                                    ]),
                                    scope: NameScopeDesc::Param,
                                    kind: None,
                                },
                                StrPosition::from_usize(24)..StrPosition::from_usize(28),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Seq(vec![
                                        NotationExpr::Ident("c".into()),
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![NotationExpr::Param(-1)]],
                                        ),
                                    ]),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::from_usize(29)..StrPosition::from_usize(33),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(34)..StrPosition::from_usize(35),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(36)..StrPosition::from_usize(37),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(38),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("c"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("c"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Param(-3),
                                            })),
                                            NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Param(-2),
                                            })),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(39)..StrPosition::from_usize(64),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(65)..StrPosition::from_usize(66),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(67)..StrPosition::from_usize(68),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(33),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("x"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Mapping(Box::new(
                                            MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Seq(vec![
                                                    NotationExpr::Ident("b".into()),
                                                    NotationExpr::Paren(
                                                        '(',
                                                        vec![vec![NotationExpr::Ident("x".into())]],
                                                    ),
                                                ]),
                                            },
                                        ))]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(34)..StrPosition::from_usize(47),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(48)..StrPosition::from_usize(49),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(50)..StrPosition::from_usize(51),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(33),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                            Input(" ↦ "),
                            WithDiag(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                (
                                    Error(Some(SyntaxError)),
                                    "a mapping target within a notation cannot reference \
                                     a standalone mapping parameter"
                                        .into(),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Mapping(Box::new(
                                            MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 2,
                                                target_expr: NotationExpr::Seq(vec![
                                                    NotationExpr::Ident("b".into()),
                                                    NotationExpr::Paren(
                                                        '(',
                                                        vec![vec![NotationExpr::Param(-2)]],
                                                    ),
                                                ]),
                                            },
                                        ))]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(34)..StrPosition::from_usize(51),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(52)..StrPosition::from_usize(53),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(54)..StrPosition::from_usize(55),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(33),
        )];
        let param_notations = vec![WithSpan::new(
            Notation {
                expr: NotationExpr::Seq(vec![
                    NotationExpr::Ident("a".into()),
                    NotationExpr::Paren(
                        '(',
                        vec![vec![NotationExpr::Mapping(Box::new(MappingNotationExpr {
                            kind: &TestInfixMapping,
                            params_len: 2,
                            target_expr: NotationExpr::Seq(vec![
                                NotationExpr::Ident("b".into()),
                                NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                            ]),
                        }))]],
                    ),
                ]),
                scope: NameScopeDesc::Global,
                kind: Some(NameKindDesc::Function),
            },
            StrPosition::from_usize(34)..StrPosition::from_usize(51),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                            Input(" ↦ "),
                            WithDiag(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                (
                                    Error(Some(SyntaxError)),
                                    "a mapping target within a notation cannot reference \
                                     a standalone mapping parameter"
                                        .into(),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations,
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(52)..StrPosition::from_usize(53),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(54)..StrPosition::from_usize(55),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(33),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDiag(
                                Box::new(WithDesc(
                                    Box::new(Input("d")),
                                    SpanDesc::NameDef(NameScopeDesc::Param, None),
                                )),
                                (
                                    Warning(Some(SyntaxWarning)),
                                    "mapping parameter name does not match parameterization; \
                                     expected `c`"
                                        .into(),
                                ),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Mapping(Box::new(
                                            MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Param(-2),
                                            },
                                        ))]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(34)..StrPosition::from_usize(47),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(48)..StrPosition::from_usize(49),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(50)..StrPosition::from_usize(51),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("c".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(17)..StrPosition::from_usize(18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(19)
                                                ..StrPosition::from_usize(20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("b".into()),
                                    NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(33),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("c")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            Input(", "),
                            WithDiag(
                                Box::new(WithDesc(
                                    Box::new(Input("d")),
                                    SpanDesc::NameDef(NameScopeDesc::Param, None),
                                )),
                                (
                                    Warning(Some(SyntaxWarning)),
                                    "mapping parameter name does not match parameterization; \
                                     expected `c`"
                                        .into(),
                                ),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("d")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Param(-2),
                                            })),
                                            NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Param(-2),
                                            })),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(34)..StrPosition::from_usize(59),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(60)..StrPosition::from_usize(61),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(62)..StrPosition::from_usize(63),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let parameterizations = vec![WithSpan::new(
            super::Parameterization {
                kind: &TestMetaModel,
                items: vec![Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: vec![WithSpan::new(
                                    super::Parameterization {
                                        kind: &TestMetaModel,
                                        items: vec![Parameterized {
                                            parameterizations: Vec::new(),
                                            prefixes: Vec::new(),
                                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                                param_notations: vec![WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("e".into()),
                                                        scope: NameScopeDesc::Param,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::from_usize(18)
                                                        ..StrPosition::from_usize(19),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::from_usize(20)
                                                            ..StrPosition::from_usize(21),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("E".into(), Unquoted)),
                                                        StrPosition::from_usize(22)
                                                            ..StrPosition::from_usize(23),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    StrPosition::from_usize(17)..StrPosition::from_usize(24),
                                )],
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Seq(vec![
                                                NotationExpr::Ident("d".into()),
                                                NotationExpr::Paren(
                                                    '(',
                                                    vec![vec![NotationExpr::Param(-1)]],
                                                ),
                                            ]),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Function),
                                        },
                                        StrPosition::from_usize(25)..StrPosition::from_usize(29),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(30)
                                                ..StrPosition::from_usize(31),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("D".into(), Unquoted)),
                                            StrPosition::from_usize(32)
                                                ..StrPosition::from_usize(33),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(16)..StrPosition::from_usize(34),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Seq(vec![
                                        NotationExpr::Ident("b".into()),
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![NotationExpr::Mapping(Box::new(
                                                MappingNotationExpr {
                                                    kind: &TestInfixMapping,
                                                    params_len: 1,
                                                    target_expr: NotationExpr::Param(-2),
                                                },
                                            ))]],
                                        ),
                                    ]),
                                    scope: NameScopeDesc::Param,
                                    kind: None,
                                },
                                StrPosition::from_usize(35)..StrPosition::from_usize(48),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Seq(vec![
                                        NotationExpr::Ident("c".into()),
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![NotationExpr::Mapping(Box::new(
                                                MappingNotationExpr {
                                                    kind: &TestPrefixMapping,
                                                    params_len: 1,
                                                    target_expr: NotationExpr::Param(-2),
                                                },
                                            ))]],
                                        ),
                                    ]),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::from_usize(49)..StrPosition::from_usize(62),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(63)..StrPosition::from_usize(64),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(65)..StrPosition::from_usize(66),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::from_usize(15)..StrPosition::from_usize(67),
        )];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("e")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : E"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("d"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("e")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("e")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("d"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("e")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("c"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("λ "),
                            WithDesc(
                                Box::new(Input("e")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(". "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("d"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("e")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("e")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("d"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("e")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("e")),
                                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                                    ),
                                    Input(" ↦ "),
                                    WithDesc(
                                        Box::new(Seq(vec![
                                            Input("d"),
                                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                            WithDesc(
                                                Box::new(Input("e")),
                                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                                            ),
                                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                        ])),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(", λ λ "),
                            WithDesc(
                                Box::new(Input("e")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(". "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("d"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    WithDesc(
                                        Box::new(Input("e")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(". "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("c"),
                                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                    Input("λ "),
                                    WithDesc(
                                        Box::new(Input("e")),
                                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                                    ),
                                    Input(". "),
                                    WithDesc(
                                        Box::new(Seq(vec![
                                            Input("d"),
                                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                                            WithDesc(
                                                Box::new(Input("e")),
                                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                                            ),
                                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                        ])),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : A"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("a".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![
                                            NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Param(-3),
                                            })),
                                            NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                                kind: &TestPrefixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Param(-2),
                                            })),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(68)..StrPosition::from_usize(131),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(132)..StrPosition::from_usize(133),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::from_usize(134)..StrPosition::from_usize(135),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
    }

    #[test]
    fn sections() {
        assert_parameter_identifier_test_output(vec![
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(&TestMetaModel),
                })),
            ),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(&TestMetaModel),
                })),
            ),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
            (
                WithDiag(
                    Box::new(Input(";")),
                    (Warning(Some(SyntaxWarning)), "superfluous semicolon".into()),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(&TestMetaModel),
                })),
            ),
            (Input(" "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDiag(
                        Box::new(Empty),
                        (Error(Some(SyntaxError)), "expected `;`".into()),
                    ),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(17)..StrPosition::from_usize(18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(&TestMetaModel),
                })),
            ),
            (Input(" "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(17)..StrPosition::from_usize(18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(&TestMetaModel),
                })),
            ),
            (Input(" "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(17)..StrPosition::from_usize(18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("y".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(24)..StrPosition::from_usize(25),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(26)..StrPosition::from_usize(27),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(28)..StrPosition::from_usize(29),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(&TestMetaModel),
                })),
            ),
            (Input(" "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("x".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(17)..StrPosition::from_usize(18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(&TestMetaModel),
                })),
            ),
            (Input(" "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("y".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(26)..StrPosition::from_usize(27),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(28)..StrPosition::from_usize(29),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(30)..StrPosition::from_usize(31),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
            (Input(" "), None),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                ]),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("a".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(16)
                                                ..StrPosition::from_usize(17),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("b".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(22)
                                                ..StrPosition::from_usize(23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(24),
                    )],
                    prefixes: Vec::new(),
                    data: Some(&TestMetaModel),
                })),
            ),
            (Input(" "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x_"),
                            WithDesc(
                                Box::new(Input("a")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("x".into()),
                                    NotationExpr::ReservedChar('_'),
                                    NotationExpr::Param(-2),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(27)..StrPosition::from_usize(30),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(33)..StrPosition::from_usize(34),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    Input("c"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("y_"),
                            WithDesc(
                                Box::new(Input("a")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input("_"),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input("_c"),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : V"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: Vec::new(),
                                    data: vec![WithSpan::new(
                                        Token(Ident("c".into(), Unquoted)),
                                        StrPosition::from_usize(37)..StrPosition::from_usize(38),
                                    )],
                                })),
                            }],
                        },
                        StrPosition::from_usize(36)..StrPosition::from_usize(39),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("y".into()),
                                    NotationExpr::ReservedChar('_'),
                                    NotationExpr::Param(-2),
                                    NotationExpr::ReservedChar('_'),
                                    NotationExpr::Param(-1),
                                    NotationExpr::ReservedChar('_'),
                                    NotationExpr::Ident("c".into()),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(40)..StrPosition::from_usize(47),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(48)..StrPosition::from_usize(49),
                            ),
                            WithSpan::new(
                                Token(Ident("V".into(), Unquoted)),
                                StrPosition::from_usize(50)..StrPosition::from_usize(51),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
            (Input(" "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("z_a")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : W"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("z".into()),
                                    NotationExpr::ReservedChar('_'),
                                    NotationExpr::Ident("a".into()),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(55)..StrPosition::from_usize(58),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(59)..StrPosition::from_usize(60),
                            ),
                            WithSpan::new(
                                Token(Ident("W".into(), Unquoted)),
                                StrPosition::from_usize(61)..StrPosition::from_usize(62),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("b_"),
                            WithDesc(
                                Box::new(Input("a")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : U; "),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                ]),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: vec![WithSpan::new(
                                    super::Parameterization {
                                        kind: &TestMetaModel,
                                        items: vec![Parameterized {
                                            parameterizations: Vec::new(),
                                            prefixes: Vec::new(),
                                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                                param_notations: vec![WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("a".into()),
                                                        scope: NameScopeDesc::Param,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::from_usize(17)
                                                        ..StrPosition::from_usize(18),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::from_usize(19)
                                                            ..StrPosition::from_usize(20),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("T".into(), Unquoted)),
                                                        StrPosition::from_usize(21)
                                                            ..StrPosition::from_usize(22),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    StrPosition::from_usize(16)..StrPosition::from_usize(23),
                                )],
                                prefixes: Vec::new(),
                                data: Some(SectionItem::Section(Section {
                                    kind: &TestMetaModel,
                                    items: vec![Parameterized {
                                        parameterizations: Vec::new(),
                                        prefixes: Vec::new(),
                                        data: Some(SectionItem::ParamGroup(ParamGroup {
                                            param_notations: vec![WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Seq(vec![
                                                        NotationExpr::Ident("b".into()),
                                                        NotationExpr::ReservedChar('_'),
                                                        NotationExpr::Param(-1),
                                                    ]),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Function),
                                                },
                                                StrPosition::from_usize(26)
                                                    ..StrPosition::from_usize(29),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(30)
                                                        ..StrPosition::from_usize(31),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("U".into(), Unquoted)),
                                                    StrPosition::from_usize(32)
                                                        ..StrPosition::from_usize(33),
                                                ),
                                            ],
                                        })),
                                    }],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(37),
                    )],
                    prefixes: Vec::new(),
                    data: Some(&TestMetaModel),
                })),
            ),
            (Input(" "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("c"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("a")),
                                SpanDesc::NameDef(NameScopeDesc::Param, None),
                            ),
                            Input(" ↦ "),
                            WithDesc(
                                Box::new(Seq(vec![
                                    Input("b_"),
                                    WithDesc(
                                        Box::new(Input("a")),
                                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                                    ),
                                ])),
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : V"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("c".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Mapping(Box::new(
                                            MappingNotationExpr {
                                                kind: &TestInfixMapping,
                                                params_len: 1,
                                                target_expr: NotationExpr::Param(-2),
                                            },
                                        ))]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(40)..StrPosition::from_usize(52),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(53)..StrPosition::from_usize(54),
                            ),
                            WithSpan::new(
                                Token(Ident("V".into(), Unquoted)),
                                StrPosition::from_usize(55)..StrPosition::from_usize(56),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
    }

    #[test]
    fn prefixes() {
        assert_parameter_identifier_test_output(vec![
            (Input("x."), None),
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Ident("x".into()),
                        StrPosition::from_usize(15)..StrPosition::from_usize(16),
                    )],
                    data: Some(&TestMetaModel),
                })),
            ),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (Input("x."), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Ident("x".into()),
                        StrPosition::from_usize(15)..StrPosition::from_usize(16),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("y".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(17)..StrPosition::from_usize(18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (Input("x.y."), None),
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: vec![
                        WithSpan::new(
                            NotationExpr::Ident("x".into()),
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        ),
                        WithSpan::new(
                            NotationExpr::Ident("y".into()),
                            StrPosition::from_usize(17)..StrPosition::from_usize(18),
                        ),
                    ],
                    data: Some(&TestMetaModel),
                })),
            ),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (Input("x."), None),
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Ident("x".into()),
                        StrPosition::from_usize(15)..StrPosition::from_usize(16),
                    )],
                    data: Some(&TestMetaModel),
                })),
            ),
            (Input(" "), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("y".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(19)..StrPosition::from_usize(20),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(21)..StrPosition::from_usize(22),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(23)..StrPosition::from_usize(24),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (Input("x."), None),
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Ident("x".into()),
                        StrPosition::from_usize(15)..StrPosition::from_usize(16),
                    )],
                    data: Some(&TestMetaModel),
                })),
            ),
            (Input(" y."), None),
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("z")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Ident("y".into()),
                        StrPosition::from_usize(19)..StrPosition::from_usize(20),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("z".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(21)..StrPosition::from_usize(22),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(23)..StrPosition::from_usize(24),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::from_usize(25)..StrPosition::from_usize(26),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (WithDesc(Box::new(Input("(")), SpanDesc::ParenStart), None),
            (Input("x y z"), None),
            (WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd), None),
            (Input("."), None),
            (
                WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Seq(vec![
                            NotationExpr::Ident("x".into()),
                            NotationExpr::Ident("y".into()),
                            NotationExpr::Ident("z".into()),
                        ]),
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    data: Some(&TestMetaModel),
                })),
            ),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input("."),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                ]),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("x".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::from_usize(23)..StrPosition::from_usize(24),
                    )],
                    data: Some(&TestMetaModel),
                })),
            ),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x y")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x y")),
                        SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input("."),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                ]),
                Some(ParameterEvent::SectionStart(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Seq(vec![
                                                NotationExpr::Ident("x".into()),
                                                NotationExpr::Ident("y".into()),
                                            ]),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(19),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(22)
                                                ..StrPosition::from_usize(23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(24),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::from_usize(25)..StrPosition::from_usize(30),
                    )],
                    data: Some(&TestMetaModel),
                })),
            ),
            (
                WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                Some(ParameterEvent::SectionEnd),
            ),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input("."),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("x".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::from_usize(23)..StrPosition::from_usize(24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("y".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(25)..StrPosition::from_usize(26),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(27)..StrPosition::from_usize(28),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input("."),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("y"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("x".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::from_usize(23)..StrPosition::from_usize(24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("y".into()),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(25)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input("."),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("y z"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("x".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::from_usize(23)..StrPosition::from_usize(24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("y".into()),
                                    NotationExpr::Ident("z".into()),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(25)..StrPosition::from_usize(30),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(33)..StrPosition::from_usize(34),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameRef(NameScopeDesc::Param, None),
                    ),
                    Input("."),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("y")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("x".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(16)
                                                ..StrPosition::from_usize(17),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("y".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(22)
                                                ..StrPosition::from_usize(23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(24),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-2),
                        StrPosition::from_usize(25)..StrPosition::from_usize(26),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Paren('(', vec![vec![NotationExpr::Param(-1)]]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(27)..StrPosition::from_usize(30),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(33)..StrPosition::from_usize(34),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input("."),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("y"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("z"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("x".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::from_usize(23)..StrPosition::from_usize(24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("y".into()),
                                    NotationExpr::Paren(
                                        '(',
                                        vec![vec![NotationExpr::Ident("z".into())]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(25)..StrPosition::from_usize(29),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(30)..StrPosition::from_usize(31),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(32)..StrPosition::from_usize(33),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input("."),
                    WithDiag(
                        Box::new(WithDesc(
                            Box::new(Input("y z")),
                            SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                        )),
                        (
                            Error(Some(SyntaxError)),
                            "a prefixed notation with an identifier sequence must be \
                             wrapped in parentheses"
                                .into(),
                        ),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("x".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::from_usize(23)..StrPosition::from_usize(24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("y".into()),
                                    NotationExpr::Ident("z".into()),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(25)..StrPosition::from_usize(28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input("."),
                    WithDiag(
                        Box::new(Seq(vec![
                            WithDesc(
                                Box::new(Input("y")),
                                SpanDesc::NameDef(NameScopeDesc::Global, None),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("z")),
                                SpanDesc::NameDef(
                                    NameScopeDesc::Global,
                                    Some(NameKindDesc::Function),
                                ),
                            ),
                        ])),
                        (
                            Error(Some(SyntaxError)),
                            "a parameter group with a prefix cannot contain multiple parameters"
                                .into(),
                        ),
                    ),
                    Input(" : U"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("x".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(16)..StrPosition::from_usize(17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(18)
                                                ..StrPosition::from_usize(19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::from_usize(20)
                                                ..StrPosition::from_usize(21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(15)..StrPosition::from_usize(22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::from_usize(23)..StrPosition::from_usize(24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("y".into()),
                                    scope: NameScopeDesc::Global,
                                    kind: None,
                                },
                                StrPosition::from_usize(25)..StrPosition::from_usize(26),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("z".into()),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::from_usize(27)..StrPosition::from_usize(28),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::from_usize(31)..StrPosition::from_usize(32),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
    }

    #[test]
    fn objects() {
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: Vec::new(),
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(22),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![ObjectItem {
                                        parameterization: super::Parameterization {
                                            kind: &TestMetaModel,
                                            items: Vec::new(),
                                        },
                                        param: Param {
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("x".into()),
                                                    scope: NameScopeDesc::Instance,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(22),
                                            )),
                                            data: Vec::new(),
                                        },
                                        extra_parts: Vec::new(),
                                    }],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(23),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" || "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("x".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(21)
                                                        ..StrPosition::from_usize(22),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("y".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(26)
                                                        ..StrPosition::from_usize(27),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(28),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" | | "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("x".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(21)
                                                        ..StrPosition::from_usize(22),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("y".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(27)
                                                        ..StrPosition::from_usize(28),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(29),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" ||"),
                    WithDiag(
                        Box::new(Input("|")),
                        (Error(Some(SyntaxError)), "superfluous separator".into()),
                    ),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("x".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(21)
                                                        ..StrPosition::from_usize(22),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("y".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(27)
                                                        ..StrPosition::from_usize(28),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(29),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                            Input("x"),
                            WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" || "),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                            Input("y"),
                            WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Paren(
                                                            '|',
                                                            vec![vec![NotationExpr::Ident(
                                                                "x".into(),
                                                            )]],
                                                        ),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(21)
                                                        ..StrPosition::from_usize(24),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Paren(
                                                            '|',
                                                            vec![vec![NotationExpr::Ident(
                                                                "y".into(),
                                                            )]],
                                                        ),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(28)
                                                        ..StrPosition::from_usize(31),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(32),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("y")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T |"),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![ObjectItem {
                                        parameterization: super::Parameterization {
                                            kind: &TestMetaModel,
                                            items: vec![Parameterized {
                                                parameterizations: Vec::new(),
                                                prefixes: Vec::new(),
                                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                                    param_notations: vec![WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("y".into()),
                                                            scope: NameScopeDesc::Field,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::from_usize(28)
                                                            ..StrPosition::from_usize(29),
                                                    )],
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::from_usize(30)
                                                                ..StrPosition::from_usize(31),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("T".into(), Unquoted)),
                                                            StrPosition::from_usize(32)
                                                                ..StrPosition::from_usize(33),
                                                        ),
                                                    ],
                                                })),
                                            }],
                                        },
                                        param: Param {
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Seq(vec![
                                                        NotationExpr::Ident("x".into()),
                                                        NotationExpr::Paren(
                                                            '(',
                                                            vec![vec![NotationExpr::Param(-1)]],
                                                        ),
                                                    ]),
                                                    scope: NameScopeDesc::Instance,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(25),
                                            )),
                                            data: Vec::new(),
                                        },
                                        extra_parts: Vec::new(),
                                    }],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(36),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("y")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T ||"),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![ObjectItem {
                                        parameterization: super::Parameterization {
                                            kind: &TestMetaModel,
                                            items: vec![Parameterized {
                                                parameterizations: Vec::new(),
                                                prefixes: Vec::new(),
                                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                                    param_notations: vec![WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("y".into()),
                                                            scope: NameScopeDesc::Field,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::from_usize(28)
                                                            ..StrPosition::from_usize(29),
                                                    )],
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::from_usize(30)
                                                                ..StrPosition::from_usize(31),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("T".into(), Unquoted)),
                                                            StrPosition::from_usize(32)
                                                                ..StrPosition::from_usize(33),
                                                        ),
                                                    ],
                                                })),
                                            }],
                                        },
                                        param: Param {
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Seq(vec![
                                                        NotationExpr::Ident("x".into()),
                                                        NotationExpr::Paren(
                                                            '(',
                                                            vec![vec![NotationExpr::Param(-1)]],
                                                        ),
                                                    ]),
                                                    scope: NameScopeDesc::Instance,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(25),
                                            )),
                                            data: Vec::new(),
                                        },
                                        extra_parts: Vec::new(),
                                    }],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(37),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("y")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T || "),
                    WithDesc(
                        Box::new(Input("z")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: vec![Parameterized {
                                                    parameterizations: Vec::new(),
                                                    prefixes: Vec::new(),
                                                    data: Some(SectionItem::ParamGroup(
                                                        ParamGroup {
                                                            param_notations: vec![WithSpan::new(
                                                                Notation {
                                                                    expr: NotationExpr::Ident(
                                                                        "y".into(),
                                                                    ),
                                                                    scope: NameScopeDesc::Field,
                                                                    kind: Some(NameKindDesc::Value),
                                                                },
                                                                StrPosition::from_usize(28)
                                                                    ..StrPosition::from_usize(29),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(30)
                                                                        ..StrPosition::from_usize(
                                                                            31,
                                                                        ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "T".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(32)
                                                                        ..StrPosition::from_usize(
                                                                            33,
                                                                        ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Seq(vec![
                                                            NotationExpr::Ident("x".into()),
                                                            NotationExpr::Paren(
                                                                '(',
                                                                vec![vec![NotationExpr::Param(-1)]],
                                                            ),
                                                        ]),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(21)
                                                        ..StrPosition::from_usize(25),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("z".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(37)
                                                        ..StrPosition::from_usize(38),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(39),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("y")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T | a | b | "),
                    WithDiag(
                        Box::new(Input("c")),
                        (Error(Some(SyntaxError)), "superfluous item part".into()),
                    ),
                    Input(" || "),
                    WithDesc(
                        Box::new(Input("z")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: vec![Parameterized {
                                                    parameterizations: Vec::new(),
                                                    prefixes: Vec::new(),
                                                    data: Some(SectionItem::ParamGroup(
                                                        ParamGroup {
                                                            param_notations: vec![WithSpan::new(
                                                                Notation {
                                                                    expr: NotationExpr::Ident(
                                                                        "y".into(),
                                                                    ),
                                                                    scope: NameScopeDesc::Field,
                                                                    kind: Some(NameKindDesc::Value),
                                                                },
                                                                StrPosition::from_usize(28)
                                                                    ..StrPosition::from_usize(29),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(30)
                                                                        ..StrPosition::from_usize(
                                                                            31,
                                                                        ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "T".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(32)
                                                                        ..StrPosition::from_usize(
                                                                            33,
                                                                        ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Seq(vec![
                                                            NotationExpr::Ident("x".into()),
                                                            NotationExpr::Paren(
                                                                '(',
                                                                vec![vec![NotationExpr::Param(-1)]],
                                                            ),
                                                        ]),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(21)
                                                        ..StrPosition::from_usize(25),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: vec![
                                                vec![Parameterized {
                                                    parameterizations: Vec::new(),
                                                    prefixes: Vec::new(),
                                                    data: Some(SectionItem::ParamGroup(
                                                        ParamGroup {
                                                            param_notations: Vec::new(),
                                                            data: vec![WithSpan::new(
                                                                Token(Ident("a".into(), Unquoted)),
                                                                StrPosition::from_usize(36)
                                                                    ..StrPosition::from_usize(37),
                                                            )],
                                                        },
                                                    )),
                                                }],
                                                vec![Parameterized {
                                                    parameterizations: Vec::new(),
                                                    prefixes: Vec::new(),
                                                    data: Some(SectionItem::ParamGroup(
                                                        ParamGroup {
                                                            param_notations: Vec::new(),
                                                            data: vec![WithSpan::new(
                                                                Token(Ident("b".into(), Unquoted)),
                                                                StrPosition::from_usize(40)
                                                                    ..StrPosition::from_usize(41),
                                                            )],
                                                        },
                                                    )),
                                                }],
                                            ],
                                        },
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("z".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(49)
                                                        ..StrPosition::from_usize(50),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(51),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("T")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("y")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T | "),
                    WithDesc(
                        Box::new(Input("z")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDiag(
                                Box::new(Empty),
                                (Error(Some(SyntaxError)), "expected `.`".into()),
                            ),
                            Input("}"),
                        ])),
                        SpanDesc::ParenEnd,
                    ),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("T".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![ObjectItem {
                                        parameterization: super::Parameterization {
                                            kind: &TestMetaModel,
                                            items: vec![Parameterized {
                                                parameterizations: Vec::new(),
                                                prefixes: Vec::new(),
                                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                                    param_notations: vec![WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("y".into()),
                                                            scope: NameScopeDesc::Field,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::from_usize(28)
                                                            ..StrPosition::from_usize(29),
                                                    )],
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::from_usize(30)
                                                                ..StrPosition::from_usize(31),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("T".into(), Unquoted)),
                                                            StrPosition::from_usize(32)
                                                                ..StrPosition::from_usize(33),
                                                        ),
                                                    ],
                                                })),
                                            }],
                                        },
                                        param: Param {
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Seq(vec![
                                                        NotationExpr::Ident("x".into()),
                                                        NotationExpr::Paren(
                                                            '(',
                                                            vec![vec![NotationExpr::Param(-1)]],
                                                        ),
                                                    ]),
                                                    scope: NameScopeDesc::Instance,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(21)
                                                    ..StrPosition::from_usize(25),
                                            )),
                                            data: Vec::new(),
                                        },
                                        extra_parts: vec![vec![Parameterized {
                                            parameterizations: Vec::new(),
                                            prefixes: Vec::new(),
                                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                                param_notations: vec![WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("z".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(36)
                                                        ..StrPosition::from_usize(37),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":=".into(), Unquoted)),
                                                        StrPosition::from_usize(38)
                                                            ..StrPosition::from_usize(40),
                                                    ),
                                                    WithSpan::new(
                                                        Mapping(super::Mapping {
                                                            kind: &TestPrefixMapping,
                                                            params: vec![MappingParam {
                                                                mappings: Vec::new(),
                                                                notation: Some(WithSpan::new(
                                                                    Notation {
                                                                        expr: NotationExpr::Ident(
                                                                            "a".into(),
                                                                        ),
                                                                        scope: NameScopeDesc::Param,
                                                                        kind: None,
                                                                    },
                                                                    StrPosition::from_usize(44)
                                                                        ..StrPosition::from_usize(
                                                                            45,
                                                                        ),
                                                                )),
                                                                data: Vec::new(),
                                                            }],
                                                        }),
                                                        StrPosition::from_usize(41)
                                                            ..StrPosition::from_usize(45),
                                                    ),
                                                ],
                                            })),
                                        }]],
                                    }],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(46),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let object_items_1 = vec![
            ObjectItem {
                parameterization: super::Parameterization {
                    kind: &TestMetaModel,
                    items: vec![Parameterized {
                        parameterizations: Vec::new(),
                        prefixes: Vec::new(),
                        data: Some(SectionItem::ParamGroup(ParamGroup {
                            param_notations: vec![WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("i".into()),
                                    scope: NameScopeDesc::Field,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::from_usize(33)..StrPosition::from_usize(34),
                            )],
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::from_usize(35)..StrPosition::from_usize(36),
                                ),
                                WithSpan::new(
                                    Token(Ident("I".into(), Unquoted)),
                                    StrPosition::from_usize(37)..StrPosition::from_usize(38),
                                ),
                            ],
                        })),
                    }],
                },
                param: Param {
                    notation: Some(WithSpan::new(
                        Notation {
                            expr: NotationExpr::Seq(vec![
                                NotationExpr::Ident("x".into()),
                                NotationExpr::ReservedChar('_'),
                                NotationExpr::Param(-1),
                            ]),
                            scope: NameScopeDesc::Instance,
                            kind: None,
                        },
                        StrPosition::from_usize(21)..StrPosition::from_usize(24),
                    )),
                    data: vec![
                        WithSpan::new(
                            Token(Ident("↦".into(), Unquoted)),
                            StrPosition::from_usize(25)..StrPosition::from_usize(28),
                        ),
                        WithSpan::new(
                            Token(Ident("i".into(), Unquoted)),
                            StrPosition::from_usize(29)..StrPosition::from_usize(30),
                        ),
                    ],
                },
                extra_parts: Vec::new(),
            },
            ObjectItem {
                parameterization: super::Parameterization {
                    kind: &TestMetaModel,
                    items: vec![
                        Parameterized {
                            parameterizations: Vec::new(),
                            prefixes: Vec::new(),
                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                param_notations: vec![WithSpan::new(
                                    Notation {
                                        expr: NotationExpr::Ident("j".into()),
                                        scope: NameScopeDesc::Field,
                                        kind: Some(NameKindDesc::Value),
                                    },
                                    StrPosition::from_usize(58)..StrPosition::from_usize(59),
                                )],
                                data: vec![
                                    WithSpan::new(
                                        Token(Ident(":".into(), Unquoted)),
                                        StrPosition::from_usize(60)..StrPosition::from_usize(61),
                                    ),
                                    WithSpan::new(
                                        Token(Ident("J".into(), Unquoted)),
                                        StrPosition::from_usize(62)..StrPosition::from_usize(63),
                                    ),
                                ],
                            })),
                        },
                        Parameterized {
                            parameterizations: Vec::new(),
                            prefixes: Vec::new(),
                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                param_notations: vec![WithSpan::new(
                                    Notation {
                                        expr: NotationExpr::Ident("k".into()),
                                        scope: NameScopeDesc::Field,
                                        kind: Some(NameKindDesc::Value),
                                    },
                                    StrPosition::from_usize(65)..StrPosition::from_usize(66),
                                )],
                                data: vec![
                                    WithSpan::new(
                                        Token(Ident(":".into(), Unquoted)),
                                        StrPosition::from_usize(67)..StrPosition::from_usize(68),
                                    ),
                                    WithSpan::new(
                                        Token(Ident("K".into(), Unquoted)),
                                        StrPosition::from_usize(69)..StrPosition::from_usize(70),
                                    ),
                                ],
                            })),
                        },
                    ],
                },
                param: Param {
                    notation: Some(WithSpan::new(
                        Notation {
                            expr: NotationExpr::Seq(vec![
                                NotationExpr::Ident("y".into()),
                                NotationExpr::ReservedChar('_'),
                                NotationExpr::Param(-2),
                                NotationExpr::ReservedChar('_'),
                                NotationExpr::Param(-1),
                            ]),
                            scope: NameScopeDesc::Instance,
                            kind: None,
                        },
                        StrPosition::from_usize(42)..StrPosition::from_usize(47),
                    )),
                    data: vec![
                        WithSpan::new(
                            Token(Ident("↦".into(), Unquoted)),
                            StrPosition::from_usize(48)..StrPosition::from_usize(51),
                        ),
                        WithSpan::new(
                            Token(Ident("j".into(), Unquoted)),
                            StrPosition::from_usize(52)..StrPosition::from_usize(53),
                        ),
                        WithSpan::new(
                            Token(Ident("k".into(), Unquoted)),
                            StrPosition::from_usize(54)..StrPosition::from_usize(55),
                        ),
                    ],
                },
                extra_parts: vec![
                    vec![Parameterized {
                        parameterizations: Vec::new(),
                        prefixes: Vec::new(),
                        data: Some(SectionItem::ParamGroup(ParamGroup {
                            param_notations: Vec::new(),
                            data: vec![WithSpan::new(
                                Token(Ident("a".into(), Unquoted)),
                                StrPosition::from_usize(73)..StrPosition::from_usize(74),
                            )],
                        })),
                    }],
                    vec![Parameterized {
                        parameterizations: Vec::new(),
                        prefixes: Vec::new(),
                        data: Some(SectionItem::ParamGroup(ParamGroup {
                            param_notations: Vec::new(),
                            data: vec![WithSpan::new(
                                Token(Ident("b".into(), Unquoted)),
                                StrPosition::from_usize(77)..StrPosition::from_usize(78),
                            )],
                        })),
                    }],
                ],
            },
        ];
        let object_items_2 = vec![ObjectItem {
            parameterization: super::Parameterization {
                kind: &TestMetaModel,
                items: Vec::new(),
            },
            param: Param {
                notation: Some(WithSpan::new(
                    Notation {
                        expr: NotationExpr::Ident("z".into()),
                        scope: NameScopeDesc::Instance,
                        kind: None,
                    },
                    StrPosition::from_usize(83)..StrPosition::from_usize(84),
                )),
                data: Vec::new(),
            },
            extra_parts: Vec::new(),
        }];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("x_"),
                            WithDesc(
                                Box::new(Input("i")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" ↦ i | "),
                    WithDesc(
                        Box::new(Input("i")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : I || "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("y_"),
                            WithDesc(
                                Box::new(Input("j")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                            Input("_"),
                            WithDesc(
                                Box::new(Input("k")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" ↦ j k | "),
                    WithDesc(
                        Box::new(Input("j")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : J; "),
                    WithDesc(
                        Box::new(Input("k")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : K | a | b"),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                    Input(" | "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("z")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("c".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: object_items_1,
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(79),
                            ),
                            WithSpan::new(
                                Token(ReservedChar('|', Isolated, Isolated)),
                                StrPosition::from_usize(80)..StrPosition::from_usize(81),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: object_items_2,
                                }),
                                StrPosition::from_usize(82)..StrPosition::from_usize(85),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("ℕ")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(WithDesc(
                            Box::new(Input("0")),
                            SpanDesc::NameDef(NameScopeDesc::Instance, None),
                        )),
                        SpanDesc::Number,
                    ),
                    Input(" || "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("S"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("n")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("n")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : ℕ"),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("ℕ".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(19)..StrPosition::from_usize(21),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("0".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(23)
                                                        ..StrPosition::from_usize(24),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: vec![Parameterized {
                                                    parameterizations: Vec::new(),
                                                    prefixes: Vec::new(),
                                                    data: Some(SectionItem::ParamGroup(
                                                        ParamGroup {
                                                            param_notations: vec![WithSpan::new(
                                                                Notation {
                                                                    expr: NotationExpr::Ident(
                                                                        "n".into(),
                                                                    ),
                                                                    scope: NameScopeDesc::Field,
                                                                    kind: Some(NameKindDesc::Value),
                                                                },
                                                                StrPosition::from_usize(35)
                                                                    ..StrPosition::from_usize(36),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(37)
                                                                        ..StrPosition::from_usize(
                                                                            38,
                                                                        ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "ℕ".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(39)
                                                                        ..StrPosition::from_usize(
                                                                            42,
                                                                        ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Seq(vec![
                                                            NotationExpr::Ident("S".into()),
                                                            NotationExpr::Paren(
                                                                '(',
                                                                vec![vec![NotationExpr::Param(-1)]],
                                                            ),
                                                        ]),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(28)
                                                        ..StrPosition::from_usize(32),
                                                )),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(22)..StrPosition::from_usize(43),
                            ),
                        ],
                    }),
                })),
            ),
            (Input("; "), None),
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("m")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("n")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : ℕ"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(
                                Box::new(Input("m")),
                                SpanDesc::NameRef(NameScopeDesc::Param, None),
                            ),
                            Input(" + "),
                            WithDesc(
                                Box::new(Input("n")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Function)),
                    ),
                    Input(" : ℕ := n."),
                    WithDesc(Box::new(Input("{")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(WithDesc(
                            Box::new(Input("0")),
                            SpanDesc::NameDef(NameScopeDesc::Instance, None),
                        )),
                        SpanDesc::Number,
                    ),
                    Input(" ↦ m || "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("S"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("x")),
                                SpanDesc::NameRef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, None),
                    ),
                    Input(" ↦ S"),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    Input("m + x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("x")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : ℕ"),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: vec![WithSpan::new(
                        super::Parameterization {
                            kind: &TestMetaModel,
                            items: vec![Parameterized {
                                parameterizations: Vec::new(),
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("m".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(46)
                                                ..StrPosition::from_usize(47),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("n".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(48)
                                                ..StrPosition::from_usize(49),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(50)
                                                ..StrPosition::from_usize(51),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("ℕ".into(), Unquoted)),
                                            StrPosition::from_usize(52)
                                                ..StrPosition::from_usize(55),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::from_usize(45)..StrPosition::from_usize(56),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Param(-2),
                                    NotationExpr::Ident("+".into()),
                                    NotationExpr::Param(-1),
                                ]),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(57)..StrPosition::from_usize(62),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(63)..StrPosition::from_usize(64),
                            ),
                            WithSpan::new(
                                Token(Ident("ℕ".into(), Unquoted)),
                                StrPosition::from_usize(65)..StrPosition::from_usize(68),
                            ),
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(69)..StrPosition::from_usize(71),
                            ),
                            WithSpan::new(
                                Token(Ident("n".into(), Unquoted)),
                                StrPosition::from_usize(72)..StrPosition::from_usize(73),
                            ),
                            WithSpan::new(
                                Token(ReservedChar('.', StronglyConnected, StronglyConnected)),
                                StrPosition::from_usize(73)..StrPosition::from_usize(74),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: vec![
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: Vec::new(),
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("0".into()),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(75)
                                                        ..StrPosition::from_usize(76),
                                                )),
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident("↦".into(), Unquoted)),
                                                        StrPosition::from_usize(77)
                                                            ..StrPosition::from_usize(80),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("m".into(), Unquoted)),
                                                        StrPosition::from_usize(81)
                                                            ..StrPosition::from_usize(82),
                                                    ),
                                                ],
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                        ObjectItem {
                                            parameterization: super::Parameterization {
                                                kind: &TestMetaModel,
                                                items: vec![Parameterized {
                                                    parameterizations: Vec::new(),
                                                    prefixes: Vec::new(),
                                                    data: Some(SectionItem::ParamGroup(
                                                        ParamGroup {
                                                            param_notations: vec![WithSpan::new(
                                                                Notation {
                                                                    expr: NotationExpr::Ident(
                                                                        "x".into(),
                                                                    ),
                                                                    scope: NameScopeDesc::Field,
                                                                    kind: Some(NameKindDesc::Value),
                                                                },
                                                                StrPosition::from_usize(106)
                                                                    ..StrPosition::from_usize(107),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(108)
                                                                        ..StrPosition::from_usize(
                                                                            109,
                                                                        ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "ℕ".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(110)
                                                                        ..StrPosition::from_usize(
                                                                            113,
                                                                        ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            },
                                            param: Param {
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Seq(vec![
                                                            NotationExpr::Ident("S".into()),
                                                            NotationExpr::Paren(
                                                                '(',
                                                                vec![vec![NotationExpr::Param(-1)]],
                                                            ),
                                                        ]),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(86)
                                                        ..StrPosition::from_usize(90),
                                                )),
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident("↦".into(), Unquoted)),
                                                        StrPosition::from_usize(91)
                                                            ..StrPosition::from_usize(94),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("S".into(), Unquoted)),
                                                        StrPosition::from_usize(95)
                                                            ..StrPosition::from_usize(96),
                                                    ),
                                                    WithSpan::new(
                                                        Paren(
                                                            '(',
                                                            vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "m".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(97)
                                                                        ..StrPosition::from_usize(
                                                                            98,
                                                                        ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "+".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(99)
                                                                        ..StrPosition::from_usize(
                                                                            100,
                                                                        ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "x".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::from_usize(101)
                                                                        ..StrPosition::from_usize(
                                                                            102,
                                                                        ),
                                                                ),
                                                            ],
                                                        ),
                                                        StrPosition::from_usize(96)
                                                            ..StrPosition::from_usize(103),
                                                    ),
                                                ],
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(74)..StrPosition::from_usize(114),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
    }

    #[test]
    fn prefix_mappings() {
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ. x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: Vec::new(),
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(23),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(24)..StrPosition::from_usize(25),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(". x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![MappingParam {
                                        mappings: Vec::new(),
                                        notation: Some(WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("a".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(23)
                                                ..StrPosition::from_usize(24),
                                        )),
                                        data: Vec::new(),
                                    }],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(25),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(26)..StrPosition::from_usize(27),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : A. x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![MappingParam {
                                        mappings: Vec::new(),
                                        notation: Some(WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("a".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::from_usize(23)
                                                ..StrPosition::from_usize(24),
                                        )),
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::from_usize(25)
                                                    ..StrPosition::from_usize(26),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("A".into(), Unquoted)),
                                                StrPosition::from_usize(27)
                                                    ..StrPosition::from_usize(28),
                                            ),
                                        ],
                                    }],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(29),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(30)..StrPosition::from_usize(31),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    Input("λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(". x, λ "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(". y"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestPrefixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("a".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(24)
                                                            ..StrPosition::from_usize(25),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(26),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(27)
                                                ..StrPosition::from_usize(28),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::from_usize(28)
                                                ..StrPosition::from_usize(29),
                                        ),
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestPrefixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("b".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(33)
                                                            ..StrPosition::from_usize(34),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(30)
                                                ..StrPosition::from_usize(35),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("y".into(), Unquoted)),
                                            StrPosition::from_usize(36)
                                                ..StrPosition::from_usize(37),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(38),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(". x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("a".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(23)
                                                    ..StrPosition::from_usize(24),
                                            )),
                                            data: Vec::new(),
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("b".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(25)
                                                    ..StrPosition::from_usize(26),
                                            )),
                                            data: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(27),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(28)..StrPosition::from_usize(29),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(",. x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("a".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(23)
                                                    ..StrPosition::from_usize(24),
                                            )),
                                            data: Vec::new(),
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("b".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(25)
                                                    ..StrPosition::from_usize(26),
                                            )),
                                            data: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(28),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDiag(
                        Box::new(Input(",")),
                        (Error(Some(SyntaxError)), "superfluous comma".into()),
                    ),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(". x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("a".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(23)
                                                    ..StrPosition::from_usize(24),
                                            )),
                                            data: Vec::new(),
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("b".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::from_usize(26)
                                                    ..StrPosition::from_usize(27),
                                            )),
                                            data: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(28),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : A, "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B. x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("a".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::from_usize(23)
                                                    ..StrPosition::from_usize(24),
                                            )),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(25)
                                                        ..StrPosition::from_usize(26),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("A".into(), Unquoted)),
                                                    StrPosition::from_usize(27)
                                                        ..StrPosition::from_usize(28),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("b".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::from_usize(30)
                                                    ..StrPosition::from_usize(31),
                                            )),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(32)
                                                        ..StrPosition::from_usize(33),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("B".into(), Unquoted)),
                                                    StrPosition::from_usize(34)
                                                        ..StrPosition::from_usize(35),
                                                ),
                                            ],
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(36),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(37)..StrPosition::from_usize(38),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDiag(
                                Box::new(Empty),
                                (Error(Some(SyntaxError)), "expected `.`".into()),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![MappingParam {
                                        mappings: Vec::new(),
                                        notation: Some(WithSpan::new(
                                            Notation {
                                                expr: NotationExpr::Ident("a".into()),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::from_usize(23)
                                                ..StrPosition::from_usize(24),
                                        )),
                                        data: Vec::new(),
                                    }],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(24),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    Input("λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDiag(
                                Box::new(Empty),
                                (Error(Some(SyntaxError)), "expected `.`".into()),
                            ),
                            Input(")"),
                        ])),
                        SpanDesc::ParenEnd,
                    ),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![WithSpan::new(
                                        Mapping(super::Mapping {
                                            kind: &TestPrefixMapping,
                                            params: vec![MappingParam {
                                                mappings: Vec::new(),
                                                notation: Some(WithSpan::new(
                                                    Notation {
                                                        expr: NotationExpr::Ident("a".into()),
                                                        scope: NameScopeDesc::Param,
                                                        kind: None,
                                                    },
                                                    StrPosition::from_usize(24)
                                                        ..StrPosition::from_usize(25),
                                                )),
                                                data: Vec::new(),
                                            }],
                                        }),
                                        StrPosition::from_usize(21)..StrPosition::from_usize(25),
                                    )],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(26),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : A, λ "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B. "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("c_"),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : C, "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D. x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("a".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::from_usize(23)
                                                    ..StrPosition::from_usize(24),
                                            )),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(25)
                                                        ..StrPosition::from_usize(26),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("A".into(), Unquoted)),
                                                    StrPosition::from_usize(27)
                                                        ..StrPosition::from_usize(28),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: vec![super::Mapping {
                                                kind: &TestPrefixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("b".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::from_usize(33)
                                                            ..StrPosition::from_usize(34),
                                                    )),
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::from_usize(35)
                                                                ..StrPosition::from_usize(36),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("B".into(), Unquoted)),
                                                            StrPosition::from_usize(37)
                                                                ..StrPosition::from_usize(38),
                                                        ),
                                                    ],
                                                }],
                                            }],
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Seq(vec![
                                                        NotationExpr::Ident("c".into()),
                                                        NotationExpr::ReservedChar('_'),
                                                        NotationExpr::Param(-1),
                                                    ]),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Function),
                                                },
                                                StrPosition::from_usize(40)
                                                    ..StrPosition::from_usize(43),
                                            )),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(44)
                                                        ..StrPosition::from_usize(45),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("C".into(), Unquoted)),
                                                    StrPosition::from_usize(46)
                                                        ..StrPosition::from_usize(47),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("d".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::from_usize(49)
                                                    ..StrPosition::from_usize(50),
                                            )),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(51)
                                                        ..StrPosition::from_usize(52),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("D".into(), Unquoted)),
                                                    StrPosition::from_usize(53)
                                                        ..StrPosition::from_usize(54),
                                                ),
                                            ],
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(55),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(56)..StrPosition::from_usize(57),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := λ "),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : A, "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B ↦ c_b : C, "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D. x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("a".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::from_usize(23)
                                                    ..StrPosition::from_usize(24),
                                            )),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(25)
                                                        ..StrPosition::from_usize(26),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("A".into(), Unquoted)),
                                                    StrPosition::from_usize(27)
                                                        ..StrPosition::from_usize(28),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("b".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::from_usize(30)
                                                    ..StrPosition::from_usize(31),
                                            )),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(32)
                                                        ..StrPosition::from_usize(33),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("B".into(), Unquoted)),
                                                    StrPosition::from_usize(34)
                                                        ..StrPosition::from_usize(35),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("↦".into(), Unquoted)),
                                                    StrPosition::from_usize(36)
                                                        ..StrPosition::from_usize(39),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("c".into(), Unquoted)),
                                                    StrPosition::from_usize(40)
                                                        ..StrPosition::from_usize(41),
                                                ),
                                                WithSpan::new(
                                                    Token(ReservedChar(
                                                        '_',
                                                        StronglyConnected,
                                                        StronglyConnected,
                                                    )),
                                                    StrPosition::from_usize(41)
                                                        ..StrPosition::from_usize(42),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("b".into(), Unquoted)),
                                                    StrPosition::from_usize(42)
                                                        ..StrPosition::from_usize(43),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(44)
                                                        ..StrPosition::from_usize(45),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("C".into(), Unquoted)),
                                                    StrPosition::from_usize(46)
                                                        ..StrPosition::from_usize(47),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: Some(WithSpan::new(
                                                Notation {
                                                    expr: NotationExpr::Ident("d".into()),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::from_usize(49)
                                                    ..StrPosition::from_usize(50),
                                            )),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::from_usize(51)
                                                        ..StrPosition::from_usize(52),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("D".into(), Unquoted)),
                                                    StrPosition::from_usize(53)
                                                        ..StrPosition::from_usize(54),
                                                ),
                                            ],
                                        },
                                    ],
                                }),
                                StrPosition::from_usize(20)..StrPosition::from_usize(55),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::from_usize(56)..StrPosition::from_usize(57),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let paren_contents = vec![
            WithSpan::new(
                Mapping(super::Mapping {
                    kind: &TestPrefixMapping,
                    params: vec![MappingParam {
                        mappings: Vec::new(),
                        notation: Some(WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("b".into()),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(25)..StrPosition::from_usize(26),
                        )),
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(27)..StrPosition::from_usize(28),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(29)..StrPosition::from_usize(30),
                            ),
                        ],
                    }],
                }),
                StrPosition::from_usize(22)..StrPosition::from_usize(31),
            ),
            WithSpan::new(
                Token(Ident("b".into(), Unquoted)),
                StrPosition::from_usize(32)..StrPosition::from_usize(33),
            ),
            WithSpan::new(
                Token(ReservedChar(',', StronglyConnected, Isolated)),
                StrPosition::from_usize(33)..StrPosition::from_usize(34),
            ),
            WithSpan::new(
                Mapping(super::Mapping {
                    kind: &TestPrefixMapping,
                    params: vec![MappingParam {
                        mappings: vec![super::Mapping {
                            kind: &TestPrefixMapping,
                            params: vec![
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: Some(WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("d".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(41)..StrPosition::from_usize(42),
                                    )),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(43)
                                                ..StrPosition::from_usize(44),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("D".into(), Unquoted)),
                                            StrPosition::from_usize(45)
                                                ..StrPosition::from_usize(46),
                                        ),
                                    ],
                                },
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: Some(WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("e".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(48)..StrPosition::from_usize(49),
                                    )),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(50)
                                                ..StrPosition::from_usize(51),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::from_usize(52)
                                                ..StrPosition::from_usize(53),
                                        ),
                                    ],
                                },
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: Some(WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("f".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(55)..StrPosition::from_usize(56),
                                    )),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(57)
                                                ..StrPosition::from_usize(58),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::from_usize(59)
                                                ..StrPosition::from_usize(60),
                                        ),
                                    ],
                                },
                            ],
                        }],
                        notation: Some(WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("c".into()),
                                    NotationExpr::Paren(
                                        '[',
                                        vec![vec![
                                            NotationExpr::Param(-3),
                                            NotationExpr::Param(-1),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(62)..StrPosition::from_usize(68),
                        )),
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(69)..StrPosition::from_usize(70),
                            ),
                            WithSpan::new(
                                Token(Ident("C".into(), Unquoted)),
                                StrPosition::from_usize(71)..StrPosition::from_usize(72),
                            ),
                        ],
                    }],
                }),
                StrPosition::from_usize(35)..StrPosition::from_usize(73),
            ),
            WithSpan::new(
                Token(Ident("c".into(), Unquoted)),
                StrPosition::from_usize(74)..StrPosition::from_usize(75),
            ),
            WithSpan::new(
                Paren(
                    '[',
                    vec![
                        WithSpan::new(
                            Token(Number("0".into())),
                            StrPosition::from_usize(76)..StrPosition::from_usize(77),
                        ),
                        WithSpan::new(
                            Token(ReservedChar(',', StronglyConnected, StronglyConnected)),
                            StrPosition::from_usize(77)..StrPosition::from_usize(78),
                        ),
                        WithSpan::new(
                            Token(Number("1".into())),
                            StrPosition::from_usize(78)..StrPosition::from_usize(79),
                        ),
                    ],
                ),
                StrPosition::from_usize(75)..StrPosition::from_usize(80),
            ),
        ];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := f"),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    Input("λ "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B. b, λ λ "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D, "),
                    WithDesc(
                        Box::new(Input("e")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : E, "),
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : E. "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("c"),
                            WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("f")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : C. c"),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("0")), SpanDesc::Number),
                    Input(","),
                    WithDesc(Box::new(Input("1")), SpanDesc::Number),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("a".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Token(Ident("f".into(), Unquoted)),
                                StrPosition::from_usize(20)..StrPosition::from_usize(21),
                            ),
                            WithSpan::new(
                                Paren('[', paren_contents),
                                StrPosition::from_usize(21)..StrPosition::from_usize(81),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
    }

    #[test]
    fn infix_mappings() {
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: Vec::new(),
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(27),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(28)
                                                ..StrPosition::from_usize(29),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(30),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("a".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(21)
                                                            ..StrPosition::from_usize(22),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(26),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(27)
                                                ..StrPosition::from_usize(28),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(29),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : A ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("a".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::from_usize(21)
                                                            ..StrPosition::from_usize(22),
                                                    )),
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::from_usize(23)
                                                                ..StrPosition::from_usize(24),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("A".into(), Unquoted)),
                                                            StrPosition::from_usize(25)
                                                                ..StrPosition::from_usize(26),
                                                        ),
                                                    ],
                                                }],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(30),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(31)
                                                ..StrPosition::from_usize(32),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(33),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("a".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(22)
                                                            ..StrPosition::from_usize(23),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(28),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(29)
                                                ..StrPosition::from_usize(30),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(31),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : A"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("a".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::from_usize(22)
                                                            ..StrPosition::from_usize(23),
                                                    )),
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::from_usize(24)
                                                                ..StrPosition::from_usize(25),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("A".into(), Unquoted)),
                                                            StrPosition::from_usize(26)
                                                                ..StrPosition::from_usize(27),
                                                        ),
                                                    ],
                                                }],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(32),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(33)
                                                ..StrPosition::from_usize(34),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(35),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            Input("b"),
                            WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Seq(vec![
                                                                NotationExpr::Ident("a".into()),
                                                                NotationExpr::Paren(
                                                                    '(',
                                                                    vec![vec![
                                                                        NotationExpr::Ident(
                                                                            "b".into(),
                                                                        ),
                                                                    ]],
                                                                ),
                                                            ]),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(21)
                                                            ..StrPosition::from_usize(25),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(29),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(30)
                                                ..StrPosition::from_usize(31),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(32),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    Input("a, "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Token(Ident("a".into(), Unquoted)),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(22),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::from_usize(22)
                                                ..StrPosition::from_usize(23),
                                        ),
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("b".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(24)
                                                            ..StrPosition::from_usize(25),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(24)
                                                ..StrPosition::from_usize(29),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(30)
                                                ..StrPosition::from_usize(31),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(32),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(" ↦ x, "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(" ↦ y"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("a".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(21)
                                                            ..StrPosition::from_usize(22),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(26),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(27)
                                                ..StrPosition::from_usize(28),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::from_usize(28)
                                                ..StrPosition::from_usize(29),
                                        ),
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("b".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(30)
                                                            ..StrPosition::from_usize(31),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(30)
                                                ..StrPosition::from_usize(35),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("y".into(), Unquoted)),
                                            StrPosition::from_usize(36)
                                                ..StrPosition::from_usize(37),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(38),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: Some(WithSpan::new(
                                                            Notation {
                                                                expr: NotationExpr::Ident(
                                                                    "a".into(),
                                                                ),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::from_usize(22)
                                                                ..StrPosition::from_usize(23),
                                                        )),
                                                        data: Vec::new(),
                                                    },
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: Some(WithSpan::new(
                                                            Notation {
                                                                expr: NotationExpr::Ident(
                                                                    "b".into(),
                                                                ),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::from_usize(24)
                                                                ..StrPosition::from_usize(25),
                                                        )),
                                                        data: Vec::new(),
                                                    },
                                                ],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(30),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(31)
                                                ..StrPosition::from_usize(32),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(33),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: Some(WithSpan::new(
                                                            Notation {
                                                                expr: NotationExpr::Ident(
                                                                    "a".into(),
                                                                ),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::from_usize(22)
                                                                ..StrPosition::from_usize(23),
                                                        )),
                                                        data: Vec::new(),
                                                    },
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: Some(WithSpan::new(
                                                            Notation {
                                                                expr: NotationExpr::Ident(
                                                                    "b".into(),
                                                                ),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::from_usize(24)
                                                                ..StrPosition::from_usize(25),
                                                        )),
                                                        data: Vec::new(),
                                                    },
                                                ],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(31),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(32)
                                                ..StrPosition::from_usize(33),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(34),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(","),
                    WithDiag(
                        Box::new(Input(",")),
                        (Error(Some(SyntaxError)), "superfluous comma".into()),
                    ),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: Some(WithSpan::new(
                                                            Notation {
                                                                expr: NotationExpr::Ident(
                                                                    "a".into(),
                                                                ),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::from_usize(22)
                                                                ..StrPosition::from_usize(23),
                                                        )),
                                                        data: Vec::new(),
                                                    },
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: Some(WithSpan::new(
                                                            Notation {
                                                                expr: NotationExpr::Ident(
                                                                    "b".into(),
                                                                ),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::from_usize(25)
                                                                ..StrPosition::from_usize(26),
                                                        )),
                                                        data: Vec::new(),
                                                    },
                                                ],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(31),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(32)
                                                ..StrPosition::from_usize(33),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(34),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : A, "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: Some(WithSpan::new(
                                                            Notation {
                                                                expr: NotationExpr::Ident(
                                                                    "a".into(),
                                                                ),
                                                                scope: NameScopeDesc::Param,
                                                                kind: Some(NameKindDesc::Value),
                                                            },
                                                            StrPosition::from_usize(22)
                                                                ..StrPosition::from_usize(23),
                                                        )),
                                                        data: vec![
                                                            WithSpan::new(
                                                                Token(Ident(":".into(), Unquoted)),
                                                                StrPosition::from_usize(24)
                                                                    ..StrPosition::from_usize(25),
                                                            ),
                                                            WithSpan::new(
                                                                Token(Ident("A".into(), Unquoted)),
                                                                StrPosition::from_usize(26)
                                                                    ..StrPosition::from_usize(27),
                                                            ),
                                                        ],
                                                    },
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: Some(WithSpan::new(
                                                            Notation {
                                                                expr: NotationExpr::Ident(
                                                                    "b".into(),
                                                                ),
                                                                scope: NameScopeDesc::Param,
                                                                kind: Some(NameKindDesc::Value),
                                                            },
                                                            StrPosition::from_usize(29)
                                                                ..StrPosition::from_usize(30),
                                                        )),
                                                        data: vec![
                                                            WithSpan::new(
                                                                Token(Ident(":".into(), Unquoted)),
                                                                StrPosition::from_usize(31)
                                                                    ..StrPosition::from_usize(32),
                                                            ),
                                                            WithSpan::new(
                                                                Token(Ident("B".into(), Unquoted)),
                                                                StrPosition::from_usize(33)
                                                                    ..StrPosition::from_usize(34),
                                                            ),
                                                        ],
                                                    },
                                                ],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(39),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(40)
                                                ..StrPosition::from_usize(41),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(42),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(" ↦ "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("a".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(21)
                                                            ..StrPosition::from_usize(22),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(26),
                                        ),
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("b".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(27)
                                                            ..StrPosition::from_usize(28),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(27)
                                                ..StrPosition::from_usize(32),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(33)
                                                ..StrPosition::from_usize(34),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(35),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    Input(" ↦ "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, None),
                    ),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: vec![super::Mapping {
                                                        kind: &TestInfixMapping,
                                                        params: vec![MappingParam {
                                                            mappings: Vec::new(),
                                                            notation: Some(WithSpan::new(
                                                                Notation {
                                                                    expr: NotationExpr::Ident(
                                                                        "a".into(),
                                                                    ),
                                                                    scope: NameScopeDesc::Param,
                                                                    kind: None,
                                                                },
                                                                StrPosition::from_usize(22)
                                                                    ..StrPosition::from_usize(23),
                                                            )),
                                                            data: Vec::new(),
                                                        }],
                                                    }],
                                                    notation: Some(WithSpan::new(
                                                        Notation {
                                                            expr: NotationExpr::Ident("b".into()),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::from_usize(28)
                                                            ..StrPosition::from_usize(29),
                                                    )),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::from_usize(21)
                                                ..StrPosition::from_usize(34),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::from_usize(35)
                                                ..StrPosition::from_usize(36),
                                        ),
                                    ],
                                ),
                                StrPosition::from_usize(20)..StrPosition::from_usize(37),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let paren_contents = vec![
            WithSpan::new(
                Mapping(super::Mapping {
                    kind: &TestInfixMapping,
                    params: vec![
                        MappingParam {
                            mappings: Vec::new(),
                            notation: Some(WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("a".into()),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::from_usize(22)..StrPosition::from_usize(23),
                            )),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::from_usize(24)..StrPosition::from_usize(25),
                                ),
                                WithSpan::new(
                                    Token(Ident("A".into(), Unquoted)),
                                    StrPosition::from_usize(26)..StrPosition::from_usize(27),
                                ),
                            ],
                        },
                        MappingParam {
                            mappings: vec![super::Mapping {
                                kind: &TestInfixMapping,
                                params: vec![MappingParam {
                                    mappings: Vec::new(),
                                    notation: Some(WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("b".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(29)..StrPosition::from_usize(30),
                                    )),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(31)
                                                ..StrPosition::from_usize(32),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(33)
                                                ..StrPosition::from_usize(34),
                                        ),
                                    ],
                                }],
                            }],
                            notation: Some(WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Seq(vec![
                                        NotationExpr::Ident("c".into()),
                                        NotationExpr::ReservedChar('_'),
                                        NotationExpr::Param(-1),
                                    ]),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::from_usize(39)..StrPosition::from_usize(42),
                            )),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::from_usize(43)..StrPosition::from_usize(44),
                                ),
                                WithSpan::new(
                                    Token(Ident("C".into(), Unquoted)),
                                    StrPosition::from_usize(45)..StrPosition::from_usize(46),
                                ),
                            ],
                        },
                        MappingParam {
                            mappings: Vec::new(),
                            notation: Some(WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("d".into()),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::from_usize(48)..StrPosition::from_usize(49),
                            )),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::from_usize(50)..StrPosition::from_usize(51),
                                ),
                                WithSpan::new(
                                    Token(Ident("D".into(), Unquoted)),
                                    StrPosition::from_usize(52)..StrPosition::from_usize(53),
                                ),
                            ],
                        },
                    ],
                }),
                StrPosition::from_usize(21)..StrPosition::from_usize(58),
            ),
            WithSpan::new(
                Token(Ident("x".into(), Unquoted)),
                StrPosition::from_usize(59)..StrPosition::from_usize(60),
            ),
        ];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : A, "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B ↦ "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("c_"),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : C, "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren('(', paren_contents),
                                StrPosition::from_usize(20)..StrPosition::from_usize(61),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let paren_contents = vec![
            WithSpan::new(
                Mapping(super::Mapping {
                    kind: &TestInfixMapping,
                    params: vec![
                        MappingParam {
                            mappings: Vec::new(),
                            notation: Some(WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("a".into()),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::from_usize(22)..StrPosition::from_usize(23),
                            )),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::from_usize(24)..StrPosition::from_usize(25),
                                ),
                                WithSpan::new(
                                    Token(Ident("A".into(), Unquoted)),
                                    StrPosition::from_usize(26)..StrPosition::from_usize(27),
                                ),
                            ],
                        },
                        MappingParam {
                            mappings: vec![super::Mapping {
                                kind: &TestPrefixMapping,
                                params: vec![MappingParam {
                                    mappings: Vec::new(),
                                    notation: Some(WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("b".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(32)..StrPosition::from_usize(33),
                                    )),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(34)
                                                ..StrPosition::from_usize(35),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::from_usize(36)
                                                ..StrPosition::from_usize(37),
                                        ),
                                    ],
                                }],
                            }],
                            notation: Some(WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Seq(vec![
                                        NotationExpr::Ident("c".into()),
                                        NotationExpr::ReservedChar('_'),
                                        NotationExpr::Param(-1),
                                    ]),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::from_usize(39)..StrPosition::from_usize(42),
                            )),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::from_usize(43)..StrPosition::from_usize(44),
                                ),
                                WithSpan::new(
                                    Token(Ident("C".into(), Unquoted)),
                                    StrPosition::from_usize(45)..StrPosition::from_usize(46),
                                ),
                            ],
                        },
                        MappingParam {
                            mappings: Vec::new(),
                            notation: Some(WithSpan::new(
                                Notation {
                                    expr: NotationExpr::Ident("d".into()),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::from_usize(48)..StrPosition::from_usize(49),
                            )),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::from_usize(50)..StrPosition::from_usize(51),
                                ),
                                WithSpan::new(
                                    Token(Ident("D".into(), Unquoted)),
                                    StrPosition::from_usize(52)..StrPosition::from_usize(53),
                                ),
                            ],
                        },
                    ],
                }),
                StrPosition::from_usize(21)..StrPosition::from_usize(58),
            ),
            WithSpan::new(
                Token(Ident("x".into(), Unquoted)),
                StrPosition::from_usize(59)..StrPosition::from_usize(60),
            ),
        ];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : A, λ "),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B. "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("c_"),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : C, "),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ x"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("f".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Paren('(', paren_contents),
                                StrPosition::from_usize(20)..StrPosition::from_usize(61),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let paren_contents = vec![
            WithSpan::new(
                Mapping(super::Mapping {
                    kind: &TestInfixMapping,
                    params: vec![MappingParam {
                        mappings: Vec::new(),
                        notation: Some(WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("b".into()),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::from_usize(23)..StrPosition::from_usize(24),
                        )),
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(25)..StrPosition::from_usize(26),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::from_usize(27)..StrPosition::from_usize(28),
                            ),
                        ],
                    }],
                }),
                StrPosition::from_usize(22)..StrPosition::from_usize(33),
            ),
            WithSpan::new(
                Token(Ident("b".into(), Unquoted)),
                StrPosition::from_usize(34)..StrPosition::from_usize(35),
            ),
            WithSpan::new(
                Token(ReservedChar(',', StronglyConnected, Isolated)),
                StrPosition::from_usize(35)..StrPosition::from_usize(36),
            ),
            WithSpan::new(
                Mapping(super::Mapping {
                    kind: &TestInfixMapping,
                    params: vec![MappingParam {
                        mappings: vec![super::Mapping {
                            kind: &TestInfixMapping,
                            params: vec![
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: Some(WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("d".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(39)..StrPosition::from_usize(40),
                                    )),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(41)
                                                ..StrPosition::from_usize(42),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("D".into(), Unquoted)),
                                            StrPosition::from_usize(43)
                                                ..StrPosition::from_usize(44),
                                        ),
                                    ],
                                },
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: Some(WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("e".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(46)..StrPosition::from_usize(47),
                                    )),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(48)
                                                ..StrPosition::from_usize(49),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::from_usize(50)
                                                ..StrPosition::from_usize(51),
                                        ),
                                    ],
                                },
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: Some(WithSpan::new(
                                        Notation {
                                            expr: NotationExpr::Ident("f".into()),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::from_usize(53)..StrPosition::from_usize(54),
                                    )),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::from_usize(55)
                                                ..StrPosition::from_usize(56),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::from_usize(57)
                                                ..StrPosition::from_usize(58),
                                        ),
                                    ],
                                },
                            ],
                        }],
                        notation: Some(WithSpan::new(
                            Notation {
                                expr: NotationExpr::Seq(vec![
                                    NotationExpr::Ident("c".into()),
                                    NotationExpr::Paren(
                                        '[',
                                        vec![vec![
                                            NotationExpr::Param(-3),
                                            NotationExpr::Param(-1),
                                        ]],
                                    ),
                                ]),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::from_usize(64)..StrPosition::from_usize(70),
                        )),
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::from_usize(71)..StrPosition::from_usize(72),
                            ),
                            WithSpan::new(
                                Token(Ident("C".into(), Unquoted)),
                                StrPosition::from_usize(73)..StrPosition::from_usize(74),
                            ),
                        ],
                    }],
                }),
                StrPosition::from_usize(37)..StrPosition::from_usize(79),
            ),
            WithSpan::new(
                Token(Ident("c".into(), Unquoted)),
                StrPosition::from_usize(80)..StrPosition::from_usize(81),
            ),
            WithSpan::new(
                Paren(
                    '[',
                    vec![
                        WithSpan::new(
                            Token(Number("0".into())),
                            StrPosition::from_usize(82)..StrPosition::from_usize(83),
                        ),
                        WithSpan::new(
                            Token(ReservedChar(',', StronglyConnected, StronglyConnected)),
                            StrPosition::from_usize(83)..StrPosition::from_usize(84),
                        ),
                        WithSpan::new(
                            Token(Number("1".into())),
                            StrPosition::from_usize(84)..StrPosition::from_usize(85),
                        ),
                    ],
                ),
                StrPosition::from_usize(81)..StrPosition::from_usize(86),
            ),
        ];
        assert_parameter_identifier_test_output(vec![
            (
                Seq(vec![
                    WithDesc(
                        Box::new(Input("a")),
                        SpanDesc::NameDef(NameScopeDesc::Global, None),
                    ),
                    Input(" := f"),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("b")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : B"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ b, "),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("d")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : D, "),
                    WithDesc(
                        Box::new(Input("e")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : E, "),
                    WithDesc(
                        Box::new(Input("f")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : E"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ "),
                    WithDesc(
                        Box::new(Seq(vec![
                            Input("c"),
                            WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("d")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(","),
                            WithDesc(
                                Box::new(Input("f")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input(")")), SpanDesc::ParenEnd),
                    Input(" ↦ c"),
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(Box::new(Input("0")), SpanDesc::Number),
                    Input(","),
                    WithDesc(Box::new(Input("1")), SpanDesc::Number),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: NotationExpr::Ident("a".into()),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::from_usize(15)..StrPosition::from_usize(16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::from_usize(17)..StrPosition::from_usize(19),
                            ),
                            WithSpan::new(
                                Token(Ident("f".into(), Unquoted)),
                                StrPosition::from_usize(20)..StrPosition::from_usize(21),
                            ),
                            WithSpan::new(
                                Paren('[', paren_contents),
                                StrPosition::from_usize(21)..StrPosition::from_usize(87),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
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
