use std::{borrow::Cow, fmt::Debug, iter::FusedIterator, mem::take, ops::Range, slice};

use lang_def::{
    mem_serializable::*,
    parser::{buffer::BufferedParserInterface, compose::*, *},
};
use lang_def_derive::MemSerializable;
use smallvec::{smallvec, SmallVec};

use crate::util::ref_stack::*;

use super::{layer1_tokenizer::*, layer2_parenthesis_matcher::*, metamodel::*};

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub enum ParameterEvent<'a, Pos: Position> {
    SectionStart(Parameterized<'a, Pos, SectionHeader<'a, Pos>>),
    SectionEnd,
    ParamGroup(Parameterized<'a, Pos, ParamGroup<'a, Pos>>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Parameterized<'a, Pos: Position, T> {
    pub parameterizations: Vec<WithSpan<Parameterization<'a, Pos>, Pos>>,
    pub data: Option<T>, // `None` in case of some parse errors
}

impl<'a, Pos: Position, T: MemSerializable<Pos>> MemSerializable<Pos>
    for Parameterized<'a, Pos, T>
{
    type Serialized = (
        <Vec<WithSpan<Parameterization<'a, Pos>, Pos>> as MemSerializable<Pos>>::Serialized,
        <Option<T> as MemSerializable<Pos>>::Serialized,
    );

    fn serialize(&self, relative_to: &Pos) -> Self::Serialized {
        (
            self.parameterizations.serialize(relative_to),
            self.data.serialize(relative_to),
        )
    }

    fn deserialize(serialized: &Self::Serialized, relative_to: &Pos) -> Self {
        Parameterized {
            parameterizations: <_>::deserialize(&serialized.0, relative_to),
            data: <_>::deserialize(&serialized.1, relative_to),
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

// TODO: parentheses after prefixes (see description)
// TODO: handle prefixes within parameterizations correctly

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct SectionHeader<'a, Pos: Position> {
    pub prefixes: Vec<WithSpan<NotationExpr<'a>, Pos>>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Section<'a, Pos: Position> {
    pub kind: &'static dyn SectionKind,
    pub header: SectionHeader<'a, Pos>,
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
    pub params: Vec<Param<'a, Pos>>,
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
    pub prefixes: Vec<NotationExpr<'a>>,
    pub expr: NotationExpr<'a>,
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
    // TODO: avoid double-matching
    pub fn find_in_sequence(&self, seq: &[Self]) -> Option<Range<usize>> {
        if let NotationExpr::Seq(exprs) = self {
            // Could be simplified once `Iterator::map_windows` is stabilized.
            let seq_len = seq.len();
            let exprs_len = exprs.len();
            if seq_len >= exprs_len {
                for idx in 0..(seq_len - exprs_len + 1) {
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
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct MappingNotationExpr<'a> {
    pub kind: &'static dyn MappingKind,
    pub params_len: usize,
    pub target_expr: NotationExpr<'a>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
struct NotationInfo<'a> {
    parameterizations: Vec<NotationExpr<'a>>,
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

        let param_notations: Vec<NotationInfo<'a>> = parameterizations
            .iter()
            .flat_map(|parameterization| ParamGroupIter::new(&parameterization.items))
            .flat_map(|group_info| {
                let parameterizations: Vec<NotationExpr<'a>> = group_info
                    .parameterizations
                    .iter()
                    .flat_map(|parameterization| ParamGroupIter::new(&parameterization.items))
                    .flat_map(|group_info| &group_info.param_group.param_notations)
                    .map(|notation| notation.expr.clone())
                    .collect();
                group_info
                    .param_group
                    .param_notations
                    .iter()
                    .map(move |notation| NotationInfo {
                        parameterizations: parameterizations.clone(),
                        notation: (**notation).clone(),
                    })
            })
            .collect();

        let (Some(item_header), _) =
            NotationContext::with_open_sections(&self.open_sections, |notation_ctx| {
                notation_ctx.with_item_iter(
                    param_notations
                        .iter()
                        .map(|notation_info| NotationContextItem::Stored { notation_info }),
                    |sub_ctx| {
                        Self::parse_section_item_header(
                            interface,
                            section_kind,
                            true,
                            None,
                            !parameterizations.is_empty(),
                            sub_ctx,
                            VarScopeDesc::Global,
                        )
                    },
                )
            })
        else {
            if !parameterizations.is_empty() {
                let span = parameterizations.first().unwrap().span()
                    ..parameterizations.last().unwrap().span();
                interface.out(
                    span,
                    ParameterEvent::ParamGroup(Parameterized {
                        parameterizations,
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
            SectionItemHeader::Section(kind, header) => {
                self.open_sections.push(OpenSection {
                    kind,
                    param_notations,
                });
                ParameterEvent::SectionStart(Parameterized {
                    parameterizations,
                    data: Some(header),
                })
            }
            SectionItemHeader::ParamGroup(param_group) => {
                ParameterEvent::ParamGroup(Parameterized {
                    parameterizations,
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
        notation_ctx: &NotationContext<'_, 'a, Pos>,
        scope: VarScopeDesc,
    ) -> SectionItems<'a, Pos> {
        let mut items = Vec::new();
        loop {
            let parameterizations = Self::parse_parameterizations(interface, section_kind);
            let (item, finished) = notation_ctx.as_restricted().with_parameterizations(
                &parameterizations,
                |sub_ctx| {
                    Self::parse_section_item(
                        interface,
                        section_kind,
                        require_semicolon_after_last,
                        separator,
                        !parameterizations.is_empty(),
                        sub_ctx,
                        scope,
                    )
                },
            );
            if item.is_some() || !parameterizations.is_empty() {
                items.push(Parameterized {
                    parameterizations,
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
        notation_ctx: &NotationContext<'_, 'a, Pos>,
        scope: VarScopeDesc,
    ) -> (Option<SectionItem<'a, Pos>>, bool) {
        let (item_header, finished) = Self::parse_section_item_header(
            interface,
            section_kind,
            require_semicolon_after_last,
            separator,
            has_parameterizations,
            notation_ctx,
            scope,
        );
        let Some(item_header) = item_header else {
            return (None, finished);
        };
        match item_header.into_inner() {
            SectionItemHeader::Section(kind, header) => {
                let items =
                    Self::parse_section_items(interface, kind, true, None, notation_ctx, scope);
                let end_token = interface.input().next().unwrap();
                assert_eq!(*end_token, TokenEvent::ParenEnd);
                (
                    Some(SectionItem::Section(Section {
                        kind,
                        header,
                        items,
                    })),
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
        notation_ctx: &NotationContext<'_, 'a, Pos>,
        scope: VarScopeDesc,
    ) -> (Option<WithSpan<SectionItemHeader<'a, Pos>, Pos>>, bool) {
        {
            let Some(start_token) = interface.input().look_ahead() else {
                if has_parameterizations {
                    let pos = interface.input().pos();
                    interface.error(
                        pos,
                        Some(ErrorKind::SyntaxError),
                        format!("expected item after parameterization"),
                    );
                }
                return (None, true);
            };
            match *start_token {
                TokenEvent::Token(Token::ReservedChar(ch, _, _))
                    if ch == ';' || Some(ch) == separator =>
                {
                    let start_token = start_token.consume();
                    if has_parameterizations {
                        interface.error(
                            start_token.span().start,
                            Some(ErrorKind::SyntaxError),
                            format!("expected item after parameterization"),
                        );
                    } else if ch == ';' {
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
                                SectionItemHeader::Section(
                                    subsection_kind,
                                    SectionHeader {
                                        prefixes: Vec::new(),
                                    },
                                ),
                                &start_token,
                            )),
                            false,
                        );
                    }
                }
                TokenEvent::ParenEnd => {
                    if has_parameterizations {
                        drop(start_token);
                        let pos = interface.input().pos();
                        interface.error(
                            pos,
                            Some(ErrorKind::SyntaxError),
                            format!("expected item after parameterization"),
                        );
                    }
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
        let mut prefix_options = section_kind.notation_prefixes();
        if let Some(options) = &prefix_options {
            if !Self::token_tree_matches_prefix_options(&start_token, options) {
                prefix_options = None;
            }
        }
        let mut span = start_token.span();
        let mut tokens = vec![start_token];
        let finished = loop {
            if let Some(prefix_options) = &prefix_options {
                if tokens.len() % 2 == 0 {
                    let mut check_section = || {
                        if let Some(paren_token) = interface.input().look_ahead() {
                            if let TokenEvent::ParenStart(paren) = *paren_token {
                                if let Some(subsection_kind) = section_kind.subsection(paren) {
                                    let paren_token = paren_token.consume();
                                    span.end = paren_token.span().end;
                                    Some(subsection_kind)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    };
                    if let Some(subsection_kind) = check_section() {
                        let mut prefixes = Vec::new();
                        for token in tokens.into_iter().step_by(2) {
                            if let Some(prefix) = Self::create_prefix_notation_expr(
                                interface,
                                token,
                                prefix_options,
                                notation_ctx,
                            ) {
                                prefixes.push(prefix);
                            }
                        }
                        return (
                            Some(WithSpan::new(
                                SectionItemHeader::Section(
                                    subsection_kind,
                                    SectionHeader { prefixes },
                                ),
                                span,
                            )),
                            false,
                        );
                    }
                }
            }
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
            if let Some(options) = &prefix_options {
                if tokens.len() % 2 == 0 {
                    if !Self::token_tree_matches_prefix_options(&token, options) {
                        prefix_options = None;
                    }
                } else {
                    if !matches!(*token, TokenTree::Token(Token::ReservedChar('.', _, _))) {
                        prefix_options = None;
                    }
                }
            }
            at_expr_start = Self::token_tree_is_notation_delimiter(&token, param_kind)
                || Self::token_tree_is_expr_prefix(&token);
            span.end = token.span().end;
            tokens.push(token);
        };

        (
            Some(WithSpan::new(
                SectionItemHeader::ParamGroup(Self::create_param_group(
                    interface,
                    tokens,
                    param_kind,
                    &prefix_options,
                    notation_ctx,
                    scope,
                )),
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
        let empty_ctx = NotationContext::new(());
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
                VarScopeDesc::Local,
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
        let parameterization = object_kind.parameterization();
        let param_data_kind = object_kind.param_data_kind();
        let empty_ctx = NotationContext::new(());
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
                        parameterization,
                        false,
                        Some(separator),
                        &empty_ctx,
                        VarScopeDesc::Field,
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
                                    VarScopeDesc::Instance,
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
            let param = NotationContext::new(()).with_section_items(
                &parameterization_items,
                VarScopeDesc::Field,
                |sub_ctx| {
                    Self::create_param(
                        interface,
                        &mut param_tokens,
                        object_kind.param_kind(),
                        sub_ctx,
                        VarScopeDesc::Instance,
                    )
                },
            );
            items.push(ObjectItem {
                parameterization: Parameterization {
                    kind: parameterization,
                    items: parameterization_items,
                },
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
                        if Self::contains_top_level_token(interface, |token| {
                            Self::token_event_is_notation_delimiter(token, param_kind)
                        }) {
                            let items = Self::parse_section_items(
                                interface,
                                parameterization,
                                false,
                                None,
                                &NotationContext::new(()),
                                VarScopeDesc::Local,
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
                        let params = Self::create_params(
                            interface,
                            &mut param_tokens,
                            mapping_kind.param_kind(),
                            &NotationContext::new(()),
                            VarScopeDesc::Local,
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
                        let params = Self::create_params(
                            interface,
                            &mut expr_tokens,
                            mapping_kind.param_kind(),
                            &NotationContext::new(()),
                            VarScopeDesc::Local,
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
        notation_ctx: &NotationContext<'_, 'a, Pos>,
        scope: VarScopeDesc,
    ) -> ParamGroup<'a, Pos> {
        let mut param_notations = Vec::new();

        let notation_delimiter_found = tokens.iter().find_map(|token| {
            if Self::token_tree_is_notation_delimiter(&token, param_kind) {
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
                if is_comma || Self::token_tree_is_notation_delimiter(&token, param_kind) {
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

        ParamGroup {
            param_notations,
            data: tokens,
        }
    }

    fn create_params<
        Pos: Position,
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        interface: &mut IF,
        tokens: &mut Tokens<'a, Pos>, // will be drained
        param_kind: &'static dyn ParamKind,
        notation_ctx: &NotationContext<'_, 'a, Pos>,
        scope: VarScopeDesc,
    ) -> Vec<Param<'a, Pos>> {
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
                    params.push(Self::create_param(
                        interface,
                        &mut param_tokens,
                        param_kind,
                        notation_ctx,
                        scope,
                    ));
                }
            } else {
                param_tokens.push(token);
            }
        }
        if !param_tokens.is_empty() {
            params.push(Self::create_param(
                interface,
                &mut param_tokens,
                param_kind,
                notation_ctx,
                scope,
            ));
        }

        params
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
        tokens: &mut Tokens<'a, Pos>, // will be drained
        param_kind: &'static dyn ParamKind,
        notation_ctx: &NotationContext<'_, 'a, Pos>,
        scope: VarScopeDesc,
    ) -> Param<'a, Pos> {
        let mut notation = Vec::new();
        let mut data = Vec::new();

        let mut token_iter = tokens.drain(..);
        while let Some(token) = token_iter.next() {
            if Self::token_tree_is_notation_delimiter(&token, param_kind) {
                if notation.is_empty() {
                    interface.error(
                        token.span().start,
                        Some(ErrorKind::SyntaxError),
                        format!("expected name/notation"),
                    );
                }
                data.push(token);
                data.extend(token_iter);
                break;
            }
            notation.push(token);
        }

        Param {
            notation: Self::create_notation(interface, &mut notation, &None, notation_ctx, scope),
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
        tokens: &mut Tokens<'a, Pos>, // will be drained
        prefix_options: &Option<NotationPrefixOptions>,
        notation_ctx: &NotationContext<'_, 'a, Pos>,
        scope: VarScopeDesc,
    ) -> Option<WithSpan<Notation<'a>, Pos>> {
        if tokens.is_empty() {
            return None;
        }

        let span = (tokens.first().unwrap()..tokens.last().unwrap()).span();
        interface.span_desc(span.clone(), SpanDesc::VarDef(scope));

        let mut prefixes = Vec::new();
        if let Some(prefix_options) = prefix_options {
            while let Some(dot_pos) = tokens.iter().position(|token| {
                matches!(**token, TokenTree::Token(Token::ReservedChar('.', _, _)))
            }) {
                let mut prefix_tokens = tokens.drain(..dot_pos + 1);
                if dot_pos == 1 {
                    if let Some(prefix) = Self::create_prefix_notation_expr(
                        interface,
                        prefix_tokens.next().unwrap(),
                        prefix_options,
                        notation_ctx,
                    ) {
                        prefixes.push(prefix.into_inner());
                    }
                } else {
                    let mut prefix_span = prefix_tokens.next().unwrap().span();
                    for token in prefix_tokens {
                        prefix_span.end = token.span().end;
                    }
                    interface.error(
                        prefix_span,
                        Some(ErrorKind::SyntaxError),
                        format!("notation prefix must be a single token or wrapped in parentheses"),
                    );
                }
            }
        }

        let expr = Self::create_notation_expr(interface, tokens, notation_ctx)?;

        if matches!(expr, NotationExpr::Param(_)) {
            interface.error(
                span,
                Some(ErrorKind::SyntaxError),
                format!("a notation cannot consist entirely of a parameter"),
            );
            return None;
        }

        Some(WithSpan::new(Notation { prefixes, expr }, span))
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
        tokens: &mut Tokens<'a, Pos>, // will be drained
        notation_ctx: &NotationContext<'_, 'a, Pos>,
    ) -> Option<NotationExpr<'a>> {
        if tokens.len() > 1 {
            let span = (tokens.first().unwrap()..tokens.last().unwrap()).span();
            let mut exprs = Vec::new();
            let mut spans = Vec::new();
            let mut token_iter = tokens.drain(..);
            while let Some(token) = token_iter.next() {
                if let TokenTree::Mapping(mapping) = &*token {
                    let mut mapping_span = token.span();
                    let mut target_tokens: Tokens<'a, Pos> = token_iter.collect();
                    if let Some(last_token) = target_tokens.last() {
                        mapping_span.end = last_token.span().end;
                    }
                    for param in &mapping.params {
                        if !param.data.is_empty() {
                            // TODO: This should actually be supported inside source parameters of
                            // (non-notation) mappings. Need a place to move this data before
                            // creating the notation.
                            interface.error(
                                param.data.first().unwrap()..param.data.last().unwrap(),
                                Some(ErrorKind::SyntaxError),
                                format!("a mapping parameter within a notation cannot be followed by additional information"),
                            );
                        }
                    }
                    if let Some(target_expr) =
                        notation_ctx
                            .as_restricted()
                            .with_params(&mapping.params, |sub_ctx| {
                                Self::create_notation_expr(interface, &mut target_tokens, sub_ctx)
                            })
                    {
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
            while let Some((range, param_idx, param_scope)) =
                notation_ctx.identify(interface, &exprs, span.clone())
            {
                let param_span = spans[range.start].start.clone()..spans[range.end - 1].end.clone();
                interface.span_desc(param_span.clone(), SpanDesc::VarRef(param_scope));
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
        notation_ctx: &NotationContext<'_, 'a, Pos>,
    ) -> Option<NotationExpr<'a>> {
        let span = token.span();
        let expr = Self::create_token_notation_expr_impl(interface, token, notation_ctx)?;
        if let Some((_, param_idx, param_scope)) =
            notation_ctx.identify(interface, slice::from_ref(&expr), span.clone())
        {
            interface.span_desc(span, SpanDesc::VarRef(param_scope));
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
        notation_ctx: &NotationContext<'_, 'a, Pos>,
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
                Token::Ident(name, _) => Some(NotationExpr::Ident(name)),
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

    fn create_prefix_notation_expr<
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
        prefix_options: &NotationPrefixOptions,
        notation_ctx: &NotationContext<'_, 'a, Pos>,
    ) -> Option<WithSpan<NotationExpr<'a>, Pos>> {
        let span = token.span();
        let expr = if matches!(
            *token,
            TokenTree::Paren(paren, _) if paren == prefix_options.paren
        ) {
            let TokenTree::Paren(_, mut inner) = token.into_inner() else {
                unreachable!()
            };
            Self::create_notation_expr(interface, &mut inner, notation_ctx)
        } else {
            Self::create_token_notation_expr(interface, token, notation_ctx)
        }?;
        Some(WithSpan::new(expr, span))
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

    fn contains_top_level_token<
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
    ) -> bool {
        let mut depth: usize = 0;
        interface
            .input()
            .look_ahead_unbounded(|token| {
                if depth == 0 && pred(token) {
                    Some(true)
                } else {
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
                }
            })
            .unwrap_or(false)
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
    ) -> bool {
        match token {
            TokenTree::Token(Token::Keyword(keyword)) => {
                param_kind.keyword_is_notation_delimiter(keyword)
            }
            TokenTree::Token(Token::Ident(identifier, IdentifierType::Unquoted)) => {
                param_kind.identifier_is_notation_delimiter(identifier)
            }
            TokenTree::Paren(paren, _) => param_kind.paren_is_notation_delimiter(*paren),
            _ => false,
        }
    }

    fn token_event_is_notation_delimiter(
        token: &TokenEvent<'a>,
        param_kind: &'static dyn ParamKind,
    ) -> bool {
        match token {
            TokenEvent::Token(Token::Keyword(keyword)) => {
                param_kind.keyword_is_notation_delimiter(keyword)
            }
            TokenEvent::Token(Token::Ident(identifier, IdentifierType::Unquoted)) => {
                param_kind.identifier_is_notation_delimiter(identifier)
            }
            TokenEvent::ParenStart(paren) => param_kind.paren_is_notation_delimiter(*paren),
            _ => false,
        }
    }

    fn token_tree_matches_prefix_options<Pos: Position>(
        token: &TokenTree<'a, Pos>,
        options: &NotationPrefixOptions,
    ) -> bool {
        matches!(
            token,
            TokenTree::Token(Token::Ident(_, _)) | TokenTree::Token(Token::Number(_))
        ) || matches!(token, TokenTree::Paren(paren, _) if *paren == options.paren)
    }
}

#[derive(MemSerializable)]
struct OpenSection<'a> {
    kind: &'static dyn SectionKind,
    param_notations: Vec<NotationInfo<'a>>,
}

enum SectionItemHeader<'a, Pos: Position> {
    Section(&'static dyn SectionKind, SectionHeader<'a, Pos>),
    ParamGroup(ParamGroup<'a, Pos>),
}

const MAX_EXPECTED_SECTION_DEPTH: usize = 4;

pub struct ParamGroupIter<'b, 'a, Pos: Position> {
    headers: SmallVec<[&'b SectionHeader<'a, Pos>; MAX_EXPECTED_SECTION_DEPTH]>,
    iters: SmallVec<
        [slice::Iter<'b, Parameterized<'a, Pos, SectionItem<'a, Pos>>>; MAX_EXPECTED_SECTION_DEPTH],
    >,
}

impl<'b, 'a, Pos: Position> ParamGroupIter<'b, 'a, Pos> {
    pub fn new(items: &'b [Parameterized<'a, Pos, SectionItem<'a, Pos>>]) -> Self {
        ParamGroupIter {
            headers: SmallVec::new(),
            iters: smallvec![items.iter()],
        }
    }
}

impl<'b, 'a, Pos: Position> Iterator for ParamGroupIter<'b, 'a, Pos> {
    type Item = ParamGroupInfo<'b, 'a, Pos>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(iter) = self.iters.last_mut() {
            if let Some(item) = iter.next() {
                if let Some(data) = &item.data {
                    match data {
                        SectionItem::Section(section) => {
                            self.headers.push(&section.header);
                            self.iters.push(section.items.iter());
                        }
                        SectionItem::ParamGroup(param_group) => {
                            return Some(ParamGroupInfo {
                                headers: self.headers.clone(),
                                parameterizations: &item.parameterizations,
                                param_group,
                            });
                        }
                    }
                }
            } else {
                self.iters.pop();
                self.headers.pop();
            }
        }
        None
    }
}

impl<'b, 'a, Pos: Position> FusedIterator for ParamGroupIter<'b, 'a, Pos> {}

pub struct ParamGroupInfo<'b, 'a, Pos: Position> {
    pub headers: SmallVec<[&'b SectionHeader<'a, Pos>; MAX_EXPECTED_SECTION_DEPTH]>,
    pub parameterizations: &'b [WithSpan<Parameterization<'a, Pos>, Pos>],
    pub param_group: &'b ParamGroup<'a, Pos>,
}

enum NotationContextItem<'b, 'a, Pos: Position> {
    Stored {
        notation_info: &'b NotationInfo<'a>,
    },
    Referenced {
        headers: SmallVec<[&'b SectionHeader<'a, Pos>; MAX_EXPECTED_SECTION_DEPTH]>,
        parameterizations: &'b [WithSpan<Parameterization<'a, Pos>, Pos>],
        notation: &'b Notation<'a>,
        scope: VarScopeDesc,
    },
}

impl<'b, 'a, Pos: Position> NotationContextItem<'b, 'a, Pos> {
    fn notation(&self) -> &Notation<'a> {
        match self {
            NotationContextItem::Stored { notation_info } => &notation_info.notation,
            NotationContextItem::Referenced { notation, .. } => notation,
        }
    }

    fn scope(&self) -> VarScopeDesc {
        match self {
            NotationContextItem::Stored { .. } => VarScopeDesc::Local,
            NotationContextItem::Referenced { scope, .. } => *scope,
        }
    }
}

type NotationContext<'b, 'a, Pos> = RefStack<NotationContextItem<'b, 'a, Pos>>;

impl<'b, 'a, Pos: Position> NotationContext<'b, 'a, Pos> {
    fn with_open_sections<R>(
        open_sections: &'b [OpenSection<'a>],
        f: impl FnOnce(&Self) -> R,
    ) -> R {
        NotationContext::new(()).with_item_iter(
            open_sections
                .iter()
                .flat_map(|open_section| &open_section.param_notations)
                .map(|notation_info| NotationContextItem::Stored { notation_info }),
            f,
        )
    }

    fn with_section_items<R>(
        &self,
        items: &'b [Parameterized<'a, Pos, SectionItem<'a, Pos>>],
        scope: VarScopeDesc,
        f: impl FnOnce(&Self) -> R,
    ) -> R {
        self.with_item_iter(
            ParamGroupIter::new(items).flat_map(|group_info| {
                group_info
                    .param_group
                    .param_notations
                    .iter()
                    .map(move |notation| NotationContextItem::Referenced {
                        headers: group_info.headers.clone(),
                        parameterizations: group_info.parameterizations,
                        notation,
                        scope,
                    })
            }),
            f,
        )
    }

    fn with_parameterizations<R>(
        &self,
        parameterizations: &'b [WithSpan<Parameterization<'a, Pos>, Pos>],
        f: impl FnOnce(&Self) -> R,
    ) -> R {
        if let Some((parameterization, rest)) = parameterizations.split_first() {
            self.with_section_items(&parameterization.items, VarScopeDesc::Local, |sub_ctx| {
                sub_ctx.with_parameterizations(rest, f)
            })
        } else {
            f(self)
        }
    }

    fn with_params<R>(&self, params: &'b [Param<'a, Pos>], f: impl FnOnce(&Self) -> R) -> R {
        self.with_item_iter(
            params
                .iter()
                .filter_map(|param| param.notation.as_ref())
                .map(|notation| NotationContextItem::Referenced {
                    headers: SmallVec::new(),
                    parameterizations: &[],
                    notation,
                    scope: VarScopeDesc::Local,
                }),
            f,
        )
    }

    fn as_restricted<'c>(&self) -> &NotationContext<'c, 'a, Pos>
    where
        'b: 'c,
    {
        // SAFETY: Existing items in the context can only be accessed via shared references, making
        // the lifetime covariant (in particular regarding the `SmallVec` in `NotationContextItem`).
        unsafe { &*(self as *const _ as *const _) }
    }

    fn identify<
        IF: ParserInterface<
            In = TokenEvent<'a>,
            Out = ParameterEvent<'a, Pos>,
            Pos = Pos,
            Config = Config,
        >,
    >(
        &self,
        interface: &mut IF,
        seq: &[NotationExpr<'a>],
        span: Range<Pos>,
    ) -> Option<(Range<usize>, ParamIdx, VarScopeDesc)> {
        let mut range = None;
        let mut result = None;
        let mut cur_idx: isize = 0;
        for item in self {
            let notation = item.notation();
            cur_idx -= 1;
            if let Some(notation_range) = notation.expr.find_in_sequence(seq) {
                if let Some(range) = &mut range {
                    match range_overlap(range, &notation_range) {
                        RangeOverlap::Disjoint | RangeOverlap::Exact | RangeOverlap::Narrowing => {}
                        RangeOverlap::Widening => {
                            *range = notation_range;
                            result = Some((cur_idx, item.scope()));
                        }
                        RangeOverlap::Overlapping => {
                            *range = notation_range;
                            result = None;
                        }
                    }
                } else {
                    range = Some(notation_range);
                    result = Some((cur_idx, item.scope()));
                }
            }
        }
        if let Some(range) = range {
            if let Some((param_idx, param_scope)) = result {
                return Some((range, param_idx, param_scope));
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
    use lang_def::parser::str::StrPosition;
    use lang_test::parser::*;

    use super::{super::metamodel::testing::TestMetaModel, *};

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
            ExpectedFragmentContent::WithDiag(
                Box::new(ExpectedFragmentContent::Empty),
                (
                    DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                    "expected keyword `%slate`".into(),
                ),
            ),
            None,
        )]);
        assert_parameter_identifier_output(vec![(
            ExpectedFragmentContent::WithDiag(
                Box::new(ExpectedFragmentContent::Input("x")),
                (
                    DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                    "expected keyword `%slate`".into(),
                ),
            ),
            None,
        )]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Empty),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "expected metamodel name".into(),
                    ),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Empty),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "expected metamodel name".into(),
                    ),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Input("x")),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "expected string".into(),
                    ),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Input("\"x\"")),
                        SpanDesc::String,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::ResourceNotFound)),
                        "unknown metamodel \"x\"".into(),
                    ),
                ),
                None,
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Empty),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "expected `;`".into(),
                    ),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Input("\"x\"")),
                        SpanDesc::String,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::ResourceNotFound)),
                        "unknown metamodel \"x\"".into(),
                    ),
                ),
                None,
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Empty),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "expected `;`".into(),
                    ),
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" x"), None),
        ]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Input("\"x\"")),
                        SpanDesc::String,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::ResourceNotFound)),
                        "unknown metamodel \"x\"".into(),
                    ),
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(";"), None),
        ]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::WithDesc(
                        Box::new(ExpectedFragmentContent::Input("\"x\"")),
                        SpanDesc::String,
                    )),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::ResourceNotFound)),
                        "unknown metamodel \"x\"".into(),
                    ),
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(";"), None),
            (ExpectedFragmentContent::Input(" x;"), None),
        ]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("\"test\"")),
                    SpanDesc::String,
                ),
                None,
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Empty),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "expected `;`".into(),
                    ),
                ),
                None,
            ),
        ]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("\"test\"")),
                    SpanDesc::String,
                ),
                None,
            ),
            (
                ExpectedFragmentContent::WithDiag(
                    Box::new(ExpectedFragmentContent::Empty),
                    (
                        DiagnosticSeverity::Error(Some(ErrorKind::SyntaxError)),
                        "expected `;`".into(),
                    ),
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::Input("x"),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: Vec::new(),
                        data: vec![WithSpan::new(
                            TokenTree::Token(Token::Ident("x".into(), IdentifierType::Unquoted)),
                            StrPosition::span_from_range(14..15),
                        )],
                    }),
                })),
            ),
            (ExpectedFragmentContent::Input(";"), None),
        ]);
        assert_parameter_identifier_output(vec![
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("%slate")),
                    SpanDesc::Keyword,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(" "), None),
            (
                ExpectedFragmentContent::WithDesc(
                    Box::new(ExpectedFragmentContent::Input("\"test\"")),
                    SpanDesc::String,
                ),
                None,
            ),
            (ExpectedFragmentContent::Input(";"), None),
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
        print_parameter_identifier_output("%slate \"test\"; [[c : C] b(c) : B] a(c ↦ b(c)) : A;");
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C; d : D] b(c,d) : B] a((c,d) ↦ b(c,d)) : A;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C; d : D] b(c,d) : B] a(c ↦ d ↦ b(c,d)) : A;",
        );
        print_parameter_identifier_output(
            "%slate \"test\"; [[c : C] { [d : D] b(c,d) : B; } e(c) : E] a(c ↦ (d ↦ b(c,d), e(c))) : A;",
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
        print_parameter_identifier_output("%slate \"test\"; a.{}");
        print_parameter_identifier_output("%slate \"test\"; (a b).{ x : T; }");
        print_parameter_identifier_output("%slate \"test\"; a.(b c).{ x : T; }");
        print_parameter_identifier_output("%slate \"test\"; a b.{}");
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
