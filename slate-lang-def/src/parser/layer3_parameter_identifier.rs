use std::{
    borrow::Cow,
    fmt::Debug,
    mem::{replace, take},
    ops::Range,
    slice,
};

use lang_def::{
    mem_serializable::*,
    parser::{buffer::BufferedParserInterface, compose::*, *},
};
use smallvec::SmallVec;

use super::{layer1_tokenizer::*, layer2_parenthesis_matcher::*, metamodel::*};

// TODO: override scope/kind of mapping params in notations (and declare as references?)
// TODO: handle prefixes within parameterizations correctly

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub enum ParameterEvent<'a, Pos: Position> {
    SectionStart(Parameterized<'a, Pos, &'static dyn SectionKind>),
    SectionEnd,
    ParamGroup(Parameterized<'a, Pos, ParamGroup<'a, Pos>>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Parameterized<'a, Pos: Position, T> {
    pub parameterizations: Vec<WithSpan<Parameterization<'a, Pos>, Pos>>,
    pub prefixes: Vec<WithSpan<NotationExpr<'a, Pos>, Pos>>,
    pub data: Option<T>, // `None` in case of some syntax errors
}

impl<'a, Pos: Position, T: MemSerializable<Pos>> MemSerializable<Pos>
    for Parameterized<'a, Pos, T>
{
    type Serialized = (
        <Vec<WithSpan<Parameterization<'a, Pos>, Pos>> as MemSerializable<Pos>>::Serialized,
        <Vec<WithSpan<NotationExpr<'a, Pos>, Pos>> as MemSerializable<Pos>>::Serialized,
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

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Section<'a, Pos: Position> {
    pub kind: &'static dyn SectionKind,
    pub items: SectionItems<'a, Pos>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Param<'a, Pos: Position> {
    pub notation: WithSpan<Notation<'a, Pos>, Pos>,
    pub data: Tokens<'a, Pos>,
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct ParamGroup<'a, Pos: Position> {
    pub param_notations: Vec<WithSpan<Notation<'a, Pos>, Pos>>,
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
    pub notation: WithSpan<Notation<'a, Pos>, Pos>,
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

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct Notation<'a, Pos: Position> {
    pub expr: Option<NotationExpr<'a, Pos>>,
    pub scope: NameScopeDesc,
    pub kind: Option<NameKindDesc>,
}

impl<'a, Pos: Position> Notation<'a, Pos> {
    fn pos_independent(&self) -> Notation<'a, ()> {
        Notation {
            expr: self.expr.as_ref().map(NotationExpr::pos_independent),
            scope: self.scope,
            kind: self.kind,
        }
    }
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub enum NotationExpr<'a, Pos: Position> {
    ReservedChar(char),
    Ident(Cow<'a, str>),
    Seq(Vec<WithSpan<NotationExpr<'a, Pos>, Pos>>),
    Paren(char, Vec<Vec<WithSpan<NotationExpr<'a, Pos>, Pos>>>),
    Mapping(Box<MappingNotationExpr<'a, Pos>>),
    Param(ParamIdx),
}

impl<'a, Pos: Position> NotationExpr<'a, Pos> {
    fn pos_independent(&self) -> NotationExpr<'a, ()> {
        match self {
            NotationExpr::ReservedChar(ch) => NotationExpr::ReservedChar(*ch),
            NotationExpr::Ident(ident) => NotationExpr::Ident(ident.clone()),
            NotationExpr::Seq(exprs) => {
                NotationExpr::Seq(exprs.iter().map(Self::pos_independent_spanned).collect())
            }
            NotationExpr::Paren(paren, rows) => NotationExpr::Paren(
                *paren,
                rows.iter()
                    .map(|cols| cols.iter().map(Self::pos_independent_spanned).collect())
                    .collect(),
            ),
            NotationExpr::Mapping(mapping) => {
                NotationExpr::Mapping(Box::new(MappingNotationExpr {
                    kind: mapping.kind,
                    params: mapping
                        .params
                        .iter()
                        .map(|_| WithSpan::new((), ()))
                        .collect(),
                    target_expr: Self::pos_independent_spanned(&mapping.target_expr),
                }))
            }
            NotationExpr::Param(idx) => NotationExpr::Param(*idx),
        }
    }

    fn pos_independent_spanned(expr: &WithSpan<Self, Pos>) -> WithSpan<NotationExpr<'a, ()>, ()> {
        WithSpan::new(expr.pos_independent(), ())
    }

    pub fn eq_content<DummyPos: Position>(&self, other: &NotationExpr<'_, DummyPos>) -> bool {
        match (self, other) {
            (NotationExpr::ReservedChar(ch0), NotationExpr::ReservedChar(ch1)) => ch0 == ch1,
            (NotationExpr::Ident(ident0), NotationExpr::Ident(ident1)) => ident0 == ident1,
            (NotationExpr::Seq(exprs0), NotationExpr::Seq(exprs1)) => {
                Self::eq_content_seq(exprs0, exprs1)
            }
            (NotationExpr::Paren(paren0, rows0), NotationExpr::Paren(paren1, rows1)) => {
                paren0 == paren1
                    && rows0.len() == rows1.len()
                    && rows0
                        .iter()
                        .zip(rows1.iter())
                        .all(|(cols0, cols1)| Self::eq_content_seq(cols0, cols1))
            }
            (NotationExpr::Mapping(mapping0), NotationExpr::Mapping(mapping1)) => {
                mapping0.kind == mapping1.kind
                    && mapping0.params.len() == mapping1.params.len()
                    && mapping0.target_expr.eq_content(&mapping1.target_expr)
            }
            (NotationExpr::Param(idx0), NotationExpr::Param(idx1)) => idx0 == idx1,
            _ => false,
        }
    }

    pub fn eq_content_seq<DummyPos: Position>(
        exprs: &[WithSpan<Self, Pos>],
        others: &[WithSpan<NotationExpr<'_, DummyPos>, DummyPos>],
    ) -> bool {
        exprs.len() == others.len()
            && exprs
                .iter()
                .zip(others.iter())
                .all(|(expr, other)| expr.eq_content(other))
    }

    pub fn find_in_sequence<DummyPos: Position>(
        &self,
        seq: &[WithSpan<NotationExpr<'_, DummyPos>, DummyPos>],
    ) -> Option<Range<usize>> {
        if let NotationExpr::Seq(exprs) = self {
            // Could be simplified once `Iterator::map_windows` is stabilized.
            let seq_len = seq.len();
            let exprs_len = exprs.len();
            if seq_len >= exprs_len {
                for idx in 0..=(seq_len - exprs_len) {
                    let range = idx..(idx + exprs_len);
                    let sub_seq = &seq[range.clone()];
                    if Self::eq_content_seq(exprs, sub_seq) {
                        return Some(range);
                    }
                }
            }
        } else {
            if let Some(idx) = seq.iter().position(|item| self.eq_content(item)) {
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
                (range.start - mapping.params.len() as isize)
                    ..(range.end - mapping.params.len() as isize),
            ),
            NotationExpr::Param(idx) => range.contains(idx),
        }
    }
}

#[derive(Clone, PartialEq, MemSerializable, Debug)]
pub struct MappingNotationExpr<'a, Pos: Position> {
    pub kind: &'static dyn MappingKind,
    pub params: Vec<WithSpan<(), Pos>>,
    pub target_expr: WithSpan<NotationExpr<'a, Pos>, Pos>,
}

// Note: It is important that notation expressions do not depend on positions, as they are a
// potentially long-lived part of the parameter identifier state, so position information would
// cause frequent re-parsing.
#[derive(Clone, PartialEq, Debug)]
struct NotationInfo<'a> {
    parameterizations_rev: Vec<Notation<'a, ()>>,
    notation: Notation<'a, ()>,
}

impl<'a, Pos> MemSerializable<Pos> for NotationInfo<'a> {
    type Serialized = (
        <Vec<Notation<'a, ()>> as MemSerializable<()>>::Serialized,
        <Notation<'a, ()> as MemSerializable<()>>::Serialized,
    );

    fn serialize(&self, _relative_to: &Pos) -> Self::Serialized {
        (
            self.parameterizations_rev.serialize(&()),
            self.notation.serialize(&()),
        )
    }

    fn deserialize(serialized: &Self::Serialized, _relative_to: &Pos) -> Self {
        NotationInfo {
            parameterizations_rev: <_>::deserialize(&serialized.0, &()),
            notation: <_>::deserialize(&serialized.1, &()),
        }
    }
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

        let param_notations_rev = Self::all_param_notations_rev(&parameterizations);
        let root_ctx = NotationContextFrame {
            entry: NotationContextEntry::OpenSections(&self.open_sections),
            parent: None,
        };
        let sub_ctx = NotationContextFrame {
            entry: NotationContextEntry::DirectRev(&param_notations_rev),
            parent: Some(&root_ctx),
        };

        let prefixes = Self::parse_prefixes(interface, section_kind, Some(&sub_ctx));

        let (Some(item_header), _) = Self::parse_section_item_header(
            interface,
            section_kind,
            true,
            None,
            !parameterizations.is_empty(),
            !prefixes.is_empty(),
            Some(&sub_ctx),
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
        notation_ctx: NotationContext<'_, 'a, Pos>,
        scope: NameScopeDesc,
    ) -> SectionItems<'a, Pos> {
        let mut items = Vec::new();
        loop {
            let parameterizations = Self::parse_parameterizations(interface, section_kind);
            let param_notations_rev = Self::all_param_notations_rev(&parameterizations);
            let sub_ctx = NotationContextFrame {
                entry: NotationContextEntry::DirectRev(&param_notations_rev),
                parent: notation_ctx,
            };
            let prefixes = Self::parse_prefixes(interface, section_kind, Some(&sub_ctx));
            let (item, finished) = Self::parse_section_item(
                interface,
                section_kind,
                require_semicolon_after_last,
                separator,
                !parameterizations.is_empty(),
                !prefixes.is_empty(),
                Some(&sub_ctx),
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
        notation_ctx: NotationContext<'_, 'a, Pos>,
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
        notation_ctx: NotationContext<'_, 'a, Pos>,
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
            let items =
                Self::parse_section_items(interface, kind, false, None, None, NameScopeDesc::Param);
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
        notation_ctx: NotationContext<'_, 'a, Pos>,
    ) -> Vec<WithSpan<NotationExpr<'a, Pos>, Pos>> {
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
                if let Some(mut prefix) =
                    Self::create_token_notation_expr(interface, token, notation_ctx)
                {
                    Self::remove_prefix_parentheses(&mut prefix, &options, true);
                    prefixes.push(prefix);
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
        let mut items = Vec::new();
        while let Some(token) = Self::parse_token_tree(interface, param_data_kind, false) {
            if Self::token_tree_is_reserved_char(&token, separator) {
                interface.error(
                    &token,
                    Some(ErrorKind::SyntaxError),
                    format!("superfluous separator"),
                );
                continue;
            }
            let mut param_tokens = vec![token];
            let mut parameterization_items = Vec::new();
            let mut extra_parts = Vec::new();
            while let Some(token) = Self::parse_token_tree(interface, param_data_kind, false) {
                if Self::token_tree_is_reserved_char(&token, separator) {
                    parameterization_items = Self::parse_section_items(
                        interface,
                        parameterization_kind,
                        false,
                        Some(separator),
                        None,
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
                                    None,
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
            let param_notations_rev = Self::param_notations_rev(&parameterization);
            let item_ctx = NotationContextFrame {
                entry: NotationContextEntry::DirectRev(&param_notations_rev),
                parent: None,
            };
            let cur_pos = param_tokens.last().unwrap().span().end;
            let param = Self::create_param(
                interface,
                &mut param_tokens,
                cur_pos,
                object_kind.param_kind(),
                Some(&item_ctx),
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
                                None,
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
                if let Token::Ident(ident, IdentifierType::Unquoted) = &token {
                    if let Some(mapping_kind) = data_kind.prefix_mapping_kind(ident) {
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
                            None,
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
                if let TokenTree::Token(Token::Ident(ident, IdentifierType::Unquoted)) = &*token {
                    if let Some(mapping_kind) = data_kind.infix_mapping_kind(ident) {
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
                            None,
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
        notation_ctx: NotationContext<'_, 'a, Pos>,
        scope: NameScopeDesc,
    ) -> ParamGroup<'a, Pos> {
        let mut param_notations = Vec::new();

        let notation_delimiter_desc = tokens.iter().find_map(|token| {
            let notation_delimiter_desc =
                Self::token_tree_is_notation_delimiter(&token, param_kind);
            if notation_delimiter_desc.is_some()
                || matches!(
                    **token,
                    TokenTree::Token(Token::Keyword(_)) | TokenTree::Token(Token::String(_, _))
                )
            {
                Some(notation_delimiter_desc)
            } else {
                None
            }
        });
        if let Some(Some(notation_delimiter_desc)) = notation_delimiter_desc {
            let mut token_iter = take(&mut tokens).into_iter();
            while let Some(token) = token_iter.next() {
                let is_comma = matches!(*token, TokenTree::Token(Token::ReservedChar(',', _, _)));
                if is_comma || Self::token_tree_is_notation_delimiter(&token, param_kind).is_some()
                {
                    let cur_pos = token.span().start;
                    if tokens.is_empty() {
                        interface.error(
                            cur_pos,
                            Some(ErrorKind::SyntaxError),
                            format!("expected name/notation"),
                        );
                    } else {
                        let notation = Self::create_notation(
                            interface,
                            &mut tokens,
                            cur_pos,
                            prefix_options,
                            notation_ctx,
                            scope,
                            notation_delimiter_desc.kind,
                            notation_delimiter_desc.is_ref,
                        );
                        param_notations.push(notation);
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
        notation_ctx: NotationContext<'_, 'a, Pos>,
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
                        token.span().start,
                        param_kind,
                        notation_ctx,
                    ));
                }
            } else {
                param_tokens.push(token);
            }
        }
        if let Some(last_token) = param_tokens.last() {
            let cur_pos = last_token.span().end;
            params.push(Self::create_mapping_param(
                interface,
                &mut param_tokens,
                cur_pos,
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
        cur_pos: Pos,
        param_kind: &'static dyn ParamKind,
        notation_ctx: NotationContext<'_, 'a, Pos>,
    ) -> MappingParam<'a, Pos> {
        if let Some(token) = tokens.first() {
            if matches!(**token, TokenTree::Mapping(_)) {
                let token = tokens.remove(0);
                let TokenTree::Mapping(mapping) = token.into_inner() else {
                    unreachable!()
                };
                let param_notations_rev = Self::mapping_param_notations_rev(&mapping.params);
                let target_ctx = NotationContextFrame {
                    entry: NotationContextEntry::Mapping(&param_notations_rev),
                    parent: notation_ctx,
                };
                let mut param = Self::create_mapping_param(
                    interface,
                    tokens,
                    cur_pos,
                    param_kind,
                    Some(&target_ctx),
                );
                param.mappings.insert(0, mapping);
                return param;
            }
        }

        let param = Self::create_param(
            interface,
            tokens,
            cur_pos,
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
        mut cur_pos: Pos,
        param_kind: &'static dyn ParamKind,
        notation_ctx: NotationContext<'_, 'a, Pos>,
        scope: NameScopeDesc,
    ) -> Param<'a, Pos> {
        let mut notation = Vec::new();
        let mut data = Vec::new();
        let mut kind = None;
        let mut is_ref = false;

        let mut token_iter = tokens.drain(..);
        while let Some(token) = token_iter.next() {
            if let Some(notation_delimiter_desc) =
                Self::token_tree_is_notation_delimiter(&token, param_kind)
            {
                cur_pos = token.span().start;
                if notation.is_empty() {
                    interface.error(
                        cur_pos.clone(),
                        Some(ErrorKind::SyntaxError),
                        format!("expected name/notation"),
                    );
                }
                data.push(token);
                data.extend(token_iter);
                kind = notation_delimiter_desc.kind;
                is_ref = notation_delimiter_desc.is_ref;
                break;
            }
            notation.push(token);
        }

        Param {
            notation: Self::create_notation(
                interface,
                &mut notation,
                cur_pos,
                &None,
                notation_ctx,
                scope,
                kind,
                is_ref,
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
        cur_pos: Pos,
        prefix_options: &Option<NotationPrefixOptions>,
        notation_ctx: NotationContext<'_, 'a, Pos>,
        scope: NameScopeDesc,
        mut kind: Option<NameKindDesc>,
        is_ref: bool,
    ) -> WithSpan<Notation<'a, Pos>, Pos> {
        if kind.is_none() && scope == NameScopeDesc::Instance {
            kind = Some(NameKindDesc::Value);
        }
        if kind.is_some() && Self::is_notation_parameterized(notation_ctx) {
            match kind {
                Some(NameKindDesc::Value) => kind = Some(NameKindDesc::Function),
                Some(NameKindDesc::Type) => kind = Some(NameKindDesc::GenericType),
                _ => {}
            }
        }

        if tokens.is_empty() {
            return WithSpan::new(
                Notation {
                    expr: None,
                    scope,
                    kind,
                },
                cur_pos,
            );
        }

        let first_token = tokens.first().unwrap();
        let last_token = tokens.last().unwrap();
        let mut span = (first_token..last_token).span();

        if tokens.len() == 1
            && matches!(
                **first_token,
                TokenTree::Token(Token::ReservedChar('_', _, _))
            )
        {
            tokens.drain(..);
            return WithSpan::new(
                Notation {
                    expr: None,
                    scope,
                    kind,
                },
                span,
            );
        }

        interface.span_desc(
            span.clone(),
            if is_ref {
                SpanDesc::NameRef(scope, kind)
            } else {
                SpanDesc::NameDef(scope, kind)
            },
        );

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

        let mut expr = Self::create_notation_expr(interface, tokens, notation_ctx);

        if let Some(expr) = &mut expr {
            if let Some(prefix_options) = prefix_options {
                Self::remove_prefix_parentheses(expr, prefix_options, false);
                span = expr.span();
            }

            if matches!(**expr, NotationExpr::Param(_)) {
                interface.error(
                    span.clone(),
                    Some(ErrorKind::SyntaxError),
                    format!("a notation cannot consist entirely of a parameter"),
                );
            }
        }

        WithSpan::new(
            Notation {
                expr: expr.map(WithSpan::into_inner),
                scope,
                kind,
            },
            span,
        )
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
        notation_ctx: NotationContext<'_, 'a, Pos>,
    ) -> Option<WithSpan<NotationExpr<'a, Pos>, Pos>> {
        if tokens.len() > 1 {
            let span = (tokens.first().unwrap()..tokens.last().unwrap()).span();
            let mut exprs = Vec::new();
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
                    let param_notations_rev = Self::mapping_param_notations_rev(&mapping.params);
                    let target_ctx = NotationContextFrame {
                        entry: NotationContextEntry::Mapping(&param_notations_rev),
                        parent: notation_ctx,
                    };
                    if let Some(target_expr) =
                        Self::create_notation_expr(interface, &mut target_tokens, Some(&target_ctx))
                    {
                        if target_expr.contains_param_ref(-(mapping.params.len() as isize)..0) {
                            interface.error(
                                target_span,
                                Some(ErrorKind::SyntaxError),
                                format!("a mapping target within a notation cannot reference a standalone mapping parameter"),
                            );
                        }
                        exprs.push(WithSpan::new(
                            NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                kind: mapping.kind,
                                params: mapping
                                    .params
                                    .iter()
                                    .map(|param| WithSpan::new((), &param.notation))
                                    .collect(),
                                target_expr,
                            })),
                            mapping_span,
                        ));
                    }
                    break;
                }
                if let Some(expr) =
                    Self::create_token_notation_expr_impl(interface, token, notation_ctx)
                {
                    exprs.push(expr);
                }
            }
            while let Some((range, param_idx, param_scope, param_kind)) =
                Self::identify_notation(interface, &exprs, span.clone(), notation_ctx)
            {
                let param_span = (&exprs[range.start]..&exprs[range.end - 1]).span();
                interface.span_desc(
                    param_span.clone(),
                    SpanDesc::NameRef(param_scope, param_kind),
                );
                if range == (0..exprs.len()) {
                    return Some(WithSpan::new(NotationExpr::Param(param_idx), param_span));
                }
                exprs.drain((range.start + 1)..range.end);
                exprs[range.start] = WithSpan::new(NotationExpr::Param(param_idx), param_span);
            }
            if exprs.len() == 1 {
                Some(exprs.pop().unwrap())
            } else {
                Some(WithSpan::new(NotationExpr::Seq(exprs), span))
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
        notation_ctx: NotationContext<'_, 'a, Pos>,
    ) -> Option<WithSpan<NotationExpr<'a, Pos>, Pos>> {
        let span = token.span();
        let expr = Self::create_token_notation_expr_impl(interface, token, notation_ctx)?;
        if let Some((_, param_idx, param_scope, param_kind)) = Self::identify_notation(
            interface,
            slice::from_ref(&expr),
            span.clone(),
            notation_ctx,
        ) {
            interface.span_desc(span.clone(), SpanDesc::NameRef(param_scope, param_kind));
            Some(WithSpan::new(NotationExpr::Param(param_idx), span))
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
        notation_ctx: NotationContext<'_, 'a, Pos>,
    ) -> Option<WithSpan<NotationExpr<'a, Pos>, Pos>> {
        let span = token.span();
        match token.into_inner() {
            TokenTree::Token(token) => match token {
                Token::ReservedChar(ch, _, _) => {
                    Some(WithSpan::new(NotationExpr::ReservedChar(ch), span))
                }
                Token::Keyword(_) => {
                    interface.error(
                        span,
                        Some(ErrorKind::SyntaxError),
                        format!("a keyword cannot be part of a notation"),
                    );
                    None
                }
                Token::Number(number) => Some(WithSpan::new(NotationExpr::Ident(number), span)),
                Token::String(_, _) => {
                    interface.error(
                        span,
                        Some(ErrorKind::SyntaxError),
                        format!("a string cannot be part of a notation"),
                    );
                    None
                }
                Token::Ident(ident, _) => Some(WithSpan::new(NotationExpr::Ident(ident), span)),
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
                Some(WithSpan::new(NotationExpr::Paren(paren, rows), span))
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

    fn remove_prefix_parentheses<Pos: Position>(
        expr: &mut WithSpan<NotationExpr<'a, Pos>, Pos>,
        options: &NotationPrefixOptions,
        allow_single_param: bool,
    ) {
        if let NotationExpr::Paren(paren, inner) = &**expr {
            if *paren == options.paren && inner.len() == 1 {
                let row = inner.first().unwrap();
                if row.len() == 1 {
                    if allow_single_param
                        || !matches!(**row.first().unwrap(), NotationExpr::Param(_))
                    {
                        let NotationExpr::Paren(_, inner) =
                            replace(&mut **expr, NotationExpr::Param(0))
                        else {
                            unreachable!()
                        };
                        *expr = inner
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
        seq: &[WithSpan<NotationExpr<'a, Pos>, Pos>],
        span: Range<Pos>,
        notation_ctx: NotationContext<'_, 'a, Pos>,
    ) -> Option<(Range<usize>, ParamIdx, NameScopeDesc, Option<NameKindDesc>)> {
        let mut range = None;
        let mut result = None;
        Self::for_each_valid_notation(notation_ctx, |idx, notation, mapping_mismatches| {
            if let Some(expr) = &notation.expr {
                if let Some(notation_range) = expr.find_in_sequence(seq) {
                    if let Some(range) = &mut range {
                        match range_overlap(range, &notation_range) {
                            RangeOverlap::Disjoint
                            | RangeOverlap::Exact
                            | RangeOverlap::Narrowing => {}
                            RangeOverlap::Widening => {
                                *range = notation_range;
                                result =
                                    Some((idx, notation.scope, notation.kind, mapping_mismatches));
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
            }
        });
        if let Some(range) = range {
            if let Some((param_idx, param_scope, param_kind, mapping_mismatches)) = result {
                let mut mapping_notation_ctx = notation_ctx;
                let mut mapping_param_idx = 0;
                for (mapping_mismatch_param_idx, mapping_mismatch_notation) in mapping_mismatches {
                    'find_param: while let Some(NotationContextFrame { entry, parent }) =
                        mapping_notation_ctx
                    {
                        let NotationContextEntry::Mapping(mapping_notation_infos_rev) = entry
                        else {
                            unreachable!();
                        };
                        for mapping_notation_info in *mapping_notation_infos_rev {
                            mapping_param_idx -= 1;
                            if mapping_param_idx == mapping_mismatch_param_idx {
                                let msg = if let Some(NotationExpr::Ident(ident)) =
                                    &mapping_mismatch_notation.expr
                                {
                                    format!("mapping parameter name does not match parameterization; expected `{ident}`")
                                } else {
                                    format!("mapping parameter notation does not match parameterization")
                                };
                                interface.warning(
                                    mapping_notation_info,
                                    Some(WarningKind::SyntaxWarning),
                                    msg,
                                );
                                break 'find_param;
                            }
                        }
                        mapping_notation_ctx = *parent;
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

    fn param_notations_rev<Pos: Position>(
        parameterization: &Parameterization<'a, Pos>,
    ) -> Vec<NotationInfo<'a>> {
        let mut param_notations_rev = Vec::new();
        Self::add_param_notations_rev(parameterization, &mut param_notations_rev);
        param_notations_rev
    }

    fn all_param_notations_rev<Pos: Position>(
        parameterizations: &[WithSpan<Parameterization<'a, Pos>, Pos>],
    ) -> Vec<NotationInfo<'a>> {
        let mut param_notations_rev = Vec::new();
        for parameterization in parameterizations.iter().rev() {
            Self::add_param_notations_rev(parameterization, &mut param_notations_rev);
        }
        param_notations_rev
    }

    fn add_param_notations_rev<Pos: Position>(
        parameterization: &Parameterization<'a, Pos>,
        param_notations_rev: &mut Vec<NotationInfo<'a>>,
    ) {
        Self::for_each_param_group_rev(
            &mut SmallVec::new(),
            &parameterization.items,
            &mut |all_parameterizations, param_group| {
                let mut parameterizations_rev = Vec::new();
                for parameterizations in all_parameterizations.iter().rev() {
                    for parameterization in parameterizations.iter().rev() {
                        Self::for_each_param_notation_rev(&parameterization.items, |notation| {
                            parameterizations_rev.push(notation.pos_independent());
                        });
                    }
                }
                for notation in param_group.param_notations.iter().rev() {
                    param_notations_rev.push(NotationInfo {
                        parameterizations_rev: parameterizations_rev.clone(),
                        notation: notation.pos_independent(),
                    });
                }
            },
        );
    }

    fn mapping_param_notations_rev<Pos: Position>(
        params: &[MappingParam<'a, Pos>],
    ) -> Vec<WithSpan<NotationInfo<'a>, Pos>> {
        params
            .iter()
            .rev()
            .map(|param| {
                WithSpan::new(
                    NotationInfo {
                        parameterizations_rev: Vec::new(),
                        notation: param.notation.pos_independent(),
                    },
                    &param.notation,
                )
            })
            .collect()
    }

    fn for_each_notation<Pos: Position>(
        mut notation_ctx: NotationContext<'_, 'a, Pos>,
        mut f: impl FnMut(usize, &NotationInfo<'a>),
    ) {
        let mut cur_idx = 0;
        while let Some(NotationContextFrame { entry, parent }) = notation_ctx {
            match entry {
                NotationContextEntry::DirectRev(notation_infos_rev) => {
                    for notation_info in *notation_infos_rev {
                        f(cur_idx, notation_info);
                        cur_idx += 1;
                    }
                }
                NotationContextEntry::OpenSections(open_sections) => {
                    for open_section in open_sections.iter().rev() {
                        for notation_info in &open_section.param_notations_rev {
                            f(cur_idx, notation_info);
                            cur_idx += 1;
                        }
                    }
                }
                NotationContextEntry::Mapping(notation_infos_rev) => {
                    for notation_info in *notation_infos_rev {
                        f(cur_idx, notation_info);
                        cur_idx += 1;
                    }
                }
            }
            notation_ctx = *parent;
        }
    }

    fn for_each_valid_notation<Pos: Position>(
        notation_ctx: NotationContext<'_, 'a, Pos>,
        mut f: impl FnMut(isize, &Notation<'a, ()>, Vec<(isize, Notation<'a, ()>)>),
    ) {
        let mapping_len = Self::mapping_len(notation_ctx);
        Self::for_each_notation(notation_ctx, |idx, notation| {
            if idx < mapping_len {
                f(!(idx as isize), &notation.notation, Vec::new());
            } else {
                let mut parameterizations_len = 0;
                let mut mapping_mismatches = Vec::new();
                let mut mapping_notation_ctx = notation_ctx;
                let mut mapping_notation_idx = 0;
                for parameterization in &notation.parameterizations_rev {
                    loop {
                        let Some(NotationContextFrame { entry, parent }) = mapping_notation_ctx
                        else {
                            break;
                        };
                        let NotationContextEntry::Mapping(notation_infos_rev) = entry else {
                            break;
                        };
                        if mapping_notation_idx < notation_infos_rev.len() {
                            let param_notation = &notation_infos_rev[mapping_notation_idx];
                            if param_notation.notation.expr != parameterization.expr {
                                mapping_mismatches.push((
                                    !(parameterizations_len as isize),
                                    parameterization.clone(),
                                ));
                            }
                            mapping_notation_idx += 1;
                            break;
                        } else {
                            mapping_notation_ctx = *parent;
                            mapping_notation_idx = 0;
                        }
                    }
                    parameterizations_len += 1;
                }
                if parameterizations_len == mapping_len {
                    f(!(idx as isize), &notation.notation, mapping_mismatches);
                }
            }
        });
    }

    fn mapping_len<Pos: Position>(mut notation_ctx: NotationContext<'_, 'a, Pos>) -> usize {
        let mut result = 0;
        while let Some(NotationContextFrame { entry, parent }) = notation_ctx {
            let NotationContextEntry::Mapping(notation_infos_rev) = entry else {
                break;
            };
            result += notation_infos_rev.len();
            notation_ctx = *parent;
        }
        result
    }

    fn is_notation_parameterized<Pos: Position>(
        mut notation_ctx: NotationContext<'_, 'a, Pos>,
    ) -> bool {
        while let Some(NotationContextFrame { entry, parent }) = notation_ctx {
            match entry {
                NotationContextEntry::DirectRev(notation_infos_rev) => {
                    if !notation_infos_rev.is_empty() {
                        return true;
                    }
                }
                NotationContextEntry::OpenSections(open_sections) => {
                    if open_sections
                        .iter()
                        .any(|open_section| !open_section.param_notations_rev.is_empty())
                    {
                        return true;
                    }
                }
                NotationContextEntry::Mapping(notation_infos_rev) => {
                    if !notation_infos_rev.is_empty() {
                        return true;
                    }
                }
            }
            notation_ctx = *parent;
        }
        false
    }

    fn for_each_param_group_rev<'b, Pos: Position>(
        parameterizations: &mut SmallVec<[&'b [WithSpan<Parameterization<'a, Pos>, Pos>]; 4]>,
        section_items: &'b [Parameterized<'a, Pos, SectionItem<'a, Pos>>],
        f: &mut impl FnMut(&[&[WithSpan<Parameterization<'a, Pos>, Pos>]], &ParamGroup<'a, Pos>),
    ) {
        for item in section_items.iter().rev() {
            parameterizations.push(&item.parameterizations);
            if let Some(data) = &item.data {
                match data {
                    SectionItem::Section(section) => {
                        Self::for_each_param_group_rev(parameterizations, &section.items, f)
                    }
                    SectionItem::ParamGroup(param_group) => {
                        f(parameterizations, param_group);
                    }
                }
            }
            parameterizations.pop();
        }
    }

    fn for_each_param_notation_rev<Pos: Position>(
        section_items: &[Parameterized<'a, Pos, SectionItem<'a, Pos>>],
        mut f: impl FnMut(&Notation<'a, Pos>),
    ) {
        Self::for_each_param_group_rev(
            &mut SmallVec::new(),
            section_items,
            &mut |_, param_group| {
                for notation in param_group.param_notations.iter().rev() {
                    f(notation);
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
            TokenTree::Token(Token::Ident(ident, IdentifierType::Unquoted)) => {
                param_kind.identifier_is_notation_delimiter(ident)
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
            TokenEvent::Token(Token::Ident(ident, IdentifierType::Unquoted)) => {
                param_kind.identifier_is_notation_delimiter(ident)
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
            TokenEvent::Token(Token::Ident(ident, IdentifierType::Unquoted)) => {
                data_kind.prefix_mapping_kind(ident).is_none()
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

type NotationContext<'b, 'a, Pos> = Option<&'b NotationContextFrame<'b, 'a, Pos>>;

struct NotationContextFrame<'b, 'a, Pos: Position> {
    entry: NotationContextEntry<'b, 'a, Pos>,
    parent: NotationContext<'b, 'a, Pos>,
}

enum NotationContextEntry<'b, 'a, Pos: Position> {
    DirectRev(&'b [NotationInfo<'a>]),
    OpenSections(&'b [OpenSection<'a>]),
    Mapping(&'b [WithSpan<NotationInfo<'a>, Pos>]),
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
                            StrPosition::span_from_range(15..16),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(17..18),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(17..18),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(21..23),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::span_from_range(24..25),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (
                Input("_ : T := y"),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: None,
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(17..18),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(21..23),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::span_from_range(24..25),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Type),
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![WithSpan::new(
                            Token(Keyword("%Type".into())),
                            StrPosition::span_from_range(17..22),
                        )],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        assert_parameter_identifier_test_output(vec![
            (Input("x."), None),
            (
                Input("T"),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Ident("x".into()),
                        StrPosition::span_from_range(15..16),
                    )],
                    data: Some(ParamGroup {
                        param_notations: Vec::new(),
                        data: vec![WithSpan::new(
                            Token(Ident("T".into(), Unquoted)),
                            StrPosition::span_from_range(17..18),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Paren(
                                    '⎿',
                                    vec![WithSpan::new(
                                        Token(Ident("T".into(), Unquoted)),
                                        StrPosition::span_from_range(20..21),
                                    )],
                                ),
                                StrPosition::span_from_range(17..24),
                            ),
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(25..27),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::span_from_range(28..29),
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
                                expr: Some(NotationExpr::Paren(
                                    '(',
                                    vec![vec![WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(16..17),
                                    )]],
                                )),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
                            ),
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(23..25),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::span_from_range(26..27),
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
                        SpanDesc::NameRef(NameScopeDesc::Global, None),
                    ),
                    Input(" ↦ y"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident("↦".into(), Unquoted)),
                                StrPosition::span_from_range(17..20),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
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
                                expr: Some(NotationExpr::Paren(
                                    '(',
                                    vec![vec![WithSpan::new(
                                        NotationExpr::Seq(vec![
                                            WithSpan::new(
                                                NotationExpr::Ident("x".into()),
                                                StrPosition::span_from_range(16..17),
                                            ),
                                            WithSpan::new(
                                                NotationExpr::Ident(":".into()),
                                                StrPosition::span_from_range(18..19),
                                            ),
                                            WithSpan::new(
                                                NotationExpr::Ident("T".into()),
                                                StrPosition::span_from_range(20..21),
                                            ),
                                        ]),
                                        StrPosition::span_from_range(16..21),
                                    )]],
                                )),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..22),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(23..25),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::span_from_range(26..27),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(17..18),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
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
                                expr: Some(NotationExpr::Ident("y".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(22..23),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(24..25),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(26..27),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("y".into()),
                                        StrPosition::span_from_range(17..18),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::ReservedChar('^'),
                                        StrPosition::span_from_range(16..17),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("y".into()),
                                        StrPosition::span_from_range(17..18),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::ReservedChar('_'),
                                        StrPosition::span_from_range(18..19),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("z".into()),
                                        StrPosition::span_from_range(19..20),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..20),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(23..24),
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
                                StrPosition::span_from_range(15..16),
                            ),
                            WithSpan::new(
                                Token(Ident("y".into(), Unquoted)),
                                StrPosition::span_from_range(17..18),
                            ),
                            WithSpan::new(
                                Token(Keyword("%z".into())),
                                StrPosition::span_from_range(19..21),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Token(Ident("a".into(), Unquoted)),
                                            StrPosition::span_from_range(22..23),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(
                                                ';',
                                                StronglyConnected,
                                                StronglyConnected,
                                            )),
                                            StrPosition::span_from_range(23..24),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("b".into(), Unquoted)),
                                            StrPosition::span_from_range(24..25),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(21..26),
                            ),
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(27..28),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren('(', Vec::new()),
                                        StrPosition::span_from_range(16..18),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren('(', Vec::new()),
                                        StrPosition::span_from_range(16..19),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..19),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(20..21),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(22..23),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("y".into()),
                                                    StrPosition::span_from_range(17..18),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Ident("z".into()),
                                                    StrPosition::span_from_range(19..20),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(16..21),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..21),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(22..23),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(24..25),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("y".into()),
                                                    StrPosition::span_from_range(17..18),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Ident("z".into()),
                                                    StrPosition::span_from_range(19..20),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(16..22),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..22),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(23..24),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(25..26),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("y".into()),
                                                    StrPosition::span_from_range(18..19),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Ident("z".into()),
                                                    StrPosition::span_from_range(20..21),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(16..23),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..23),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(24..25),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(26..27),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("y".into()),
                                                    StrPosition::span_from_range(17..18),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Ident("z".into()),
                                                    StrPosition::span_from_range(20..21),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(16..23),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..23),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(24..25),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(26..27),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("y".into()),
                                                    StrPosition::span_from_range(17..18),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Ident("z".into()),
                                                    StrPosition::span_from_range(19..20),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(16..23),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..23),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(24..25),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(26..27),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![
                                                vec![WithSpan::new(
                                                    NotationExpr::Ident("y".into()),
                                                    StrPosition::span_from_range(17..18),
                                                )],
                                                vec![WithSpan::new(
                                                    NotationExpr::Ident("z".into()),
                                                    StrPosition::span_from_range(19..20),
                                                )],
                                            ],
                                        ),
                                        StrPosition::span_from_range(16..21),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..21),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(22..23),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(24..25),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(15..16),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Ident("42".into()),
                                                StrPosition::span_from_range(17..19),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(16..20),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..20),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(23..24),
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
                                    expr: Some(NotationExpr::Ident("x".into())),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(15..16),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Ident("y".into())),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(17..18),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
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
                    Input(","),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Global, Some(NameKindDesc::Value)),
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
                                    expr: Some(NotationExpr::Ident("x".into())),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(15..16),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Ident("y".into())),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(17..18),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(20..21),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(22..23),
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
                                    expr: Some(NotationExpr::Ident("x".into())),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(15..16),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Ident("y".into())),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(18..19),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(20..21),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(22..23),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(16..17),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(18..19),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(20..21),
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
                                expr: Some(NotationExpr::Ident("42".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(15..17),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(18..19),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(20..21),
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
                                            expr: Some(NotationExpr::Ident("b".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("a".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(23..24),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(25..26),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(27..28),
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
                                            expr: Some(NotationExpr::Ident("b".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Param(-1)),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(23..24),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(25..26),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(27..28),
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
                                            expr: Some(NotationExpr::Ident("b".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("a".into()),
                                        StrPosition::span_from_range(23..24),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(25..26),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(24..27),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(23..27),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(28..29),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(30..31),
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
                                            expr: Some(NotationExpr::Seq(vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("b".into()),
                                                    StrPosition::span_from_range(16..17),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Ident("c".into()),
                                                    StrPosition::span_from_range(18..19),
                                                ),
                                            ])),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..19),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(22..23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..24),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("a".into()),
                                        StrPosition::span_from_range(25..26),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(27..30),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(26..31),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(25..31),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(32..33),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(34..35),
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
                    Input(", "),
                    WithDesc(
                        Box::new(Input("b c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(" a"),
                            WithDesc(Box::new(Input("(")), SpanDesc::ParenStart),
                            WithDesc(
                                Box::new(Input("b c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Input("c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(" "),
                            WithDesc(
                                Box::new(Input("b c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                            ),
                            Input(", "),
                            WithDesc(
                                Box::new(Input("b c")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                                                expr: Some(NotationExpr::Ident("b".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(16..17),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Seq(vec![
                                                    WithSpan::new(
                                                        NotationExpr::Ident("b".into()),
                                                        StrPosition::span_from_range(19..20),
                                                    ),
                                                    WithSpan::new(
                                                        NotationExpr::Ident("c".into()),
                                                        StrPosition::span_from_range(21..22),
                                                    ),
                                                ])),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(19..22),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(24..25),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(26..27),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(28..29),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Param(-1),
                                        StrPosition::span_from_range(31..32),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Param(-3),
                                        StrPosition::span_from_range(33..34),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("a".into()),
                                        StrPosition::span_from_range(35..36),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Param(-2),
                                                    StrPosition::span_from_range(37..40),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Param(-3),
                                                    StrPosition::span_from_range(42..43),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(45..46),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Seq(vec![
                                                        WithSpan::new(
                                                            NotationExpr::Param(-3),
                                                            StrPosition::span_from_range(48..49),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::Param(-2),
                                                            StrPosition::span_from_range(50..53),
                                                        ),
                                                    ]),
                                                    StrPosition::span_from_range(48..53),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Seq(vec![
                                                        WithSpan::new(
                                                            NotationExpr::Param(-2),
                                                            StrPosition::span_from_range(55..58),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::Param(-1),
                                                            StrPosition::span_from_range(59..60),
                                                        ),
                                                    ]),
                                                    StrPosition::span_from_range(55..60),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(36..61),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(31..61),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(62..63),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(64..65),
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
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                                                expr: Some(NotationExpr::Ident("b".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(16..17),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(18..19),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(22..23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..24),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Param(-2),
                                        StrPosition::span_from_range(25..26),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("+".into()),
                                        StrPosition::span_from_range(27..28),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Param(-1),
                                        StrPosition::span_from_range(29..30),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(25..30),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(33..34),
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
                    Input(" : B; "),
                    WithDesc(
                        Box::new(Input("c")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
                    ),
                    Input(" : C"),
                    WithDesc(Box::new(Input("]")), SpanDesc::ParenEnd),
                    Input(" "),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                            items: vec![
                                Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("b".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(16..17),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(18..19),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("B".into(), Unquoted)),
                                                StrPosition::span_from_range(20..21),
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
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(23..24),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(25..26),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::span_from_range(27..28),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::span_from_range(15..29),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Param(-2),
                                        StrPosition::span_from_range(30..31),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("+".into()),
                                        StrPosition::span_from_range(32..33),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Param(-1),
                                        StrPosition::span_from_range(34..35),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(30..35),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(36..37),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(38..39),
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
                            WithDesc(
                                Box::new(Input("b")),
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                    parameterizations: vec![
                        WithSpan::new(
                            super::Parameterization {
                                kind: &TestMetaModel,
                                items: vec![Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("b".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(16..17),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(18..19),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("B".into(), Unquoted)),
                                                StrPosition::span_from_range(20..21),
                                            ),
                                        ],
                                    })),
                                }],
                            },
                            StrPosition::span_from_range(15..22),
                        ),
                        WithSpan::new(
                            super::Parameterization {
                                kind: &TestMetaModel,
                                items: vec![Parameterized {
                                    parameterizations: Vec::new(),
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(24..25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(26..27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::span_from_range(28..29),
                                            ),
                                        ],
                                    })),
                                }],
                            },
                            StrPosition::span_from_range(23..30),
                        ),
                    ],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Param(-2),
                                        StrPosition::span_from_range(31..32),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("+".into()),
                                        StrPosition::span_from_range(33..34),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Param(-1),
                                        StrPosition::span_from_range(35..36),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(31..36),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(37..38),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(39..40),
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
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                                                expr: Some(NotationExpr::Seq(vec![
                                                    WithSpan::new(
                                                        NotationExpr::Ident("a".into()),
                                                        StrPosition::span_from_range(16..17),
                                                    ),
                                                    WithSpan::new(
                                                        NotationExpr::Ident("b".into()),
                                                        StrPosition::span_from_range(18..19),
                                                    ),
                                                ])),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(16..19),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Seq(vec![
                                                    WithSpan::new(
                                                        NotationExpr::Ident("b".into()),
                                                        StrPosition::span_from_range(21..22),
                                                    ),
                                                    WithSpan::new(
                                                        NotationExpr::Ident("c".into()),
                                                        StrPosition::span_from_range(23..24),
                                                    ),
                                                ])),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(21..24),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(25..26),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(27..28),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..29),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("a".into()),
                                        StrPosition::span_from_range(30..31),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(32..33),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("c".into()),
                                        StrPosition::span_from_range(34..35),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(30..35),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(36..37),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(38..39),
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
                                                        expr: Some(NotationExpr::Ident("d".into())),
                                                        scope: NameScopeDesc::Param,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(17..18),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::span_from_range(19..20),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("D".into(), Unquoted)),
                                                        StrPosition::span_from_range(21..22),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    StrPosition::span_from_range(16..23),
                                )],
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![
                                        WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("b".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Function),
                                            },
                                            StrPosition::span_from_range(24..25),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Function),
                                            },
                                            StrPosition::span_from_range(26..27),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(28..29),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(30..31),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..32),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("a".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(33..34),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(35..36),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(37..38),
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
                                                            expr: Some(NotationExpr::Ident(
                                                                "d".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::span_from_range(17..18),
                                                    )],
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::span_from_range(19..20),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("D".into(), Unquoted)),
                                                            StrPosition::span_from_range(21..22),
                                                        ),
                                                    ],
                                                })),
                                            }],
                                        },
                                        StrPosition::span_from_range(16..23),
                                    )],
                                    prefixes: Vec::new(),
                                    data: Some(SectionItem::ParamGroup(ParamGroup {
                                        param_notations: vec![WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("b".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Function),
                                            },
                                            StrPosition::span_from_range(24..25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(26..27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("B".into(), Unquoted)),
                                                StrPosition::span_from_range(28..29),
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
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(31..32),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(33..34),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::span_from_range(35..36),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::span_from_range(15..37),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("a".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(38..39),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(40..41),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(42..43),
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
                                expr: Some(NotationExpr::Ident("a".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                    expr: Some(NotationExpr::Ident("b".into())),
                                                    scope: NameScopeDesc::Local,
                                                    kind: None,
                                                },
                                                StrPosition::span_from_range(21..22),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":=".into(), Unquoted)),
                                                    StrPosition::span_from_range(23..25),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("c".into(), Unquoted)),
                                                    StrPosition::span_from_range(26..27),
                                                ),
                                            ],
                                        })),
                                    }],
                                }),
                                StrPosition::span_from_range(20..28),
                            ),
                            WithSpan::new(
                                Token(Ident("b".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
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
                                expr: Some(NotationExpr::Ident("a".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                    expr: Some(NotationExpr::Ident("c".into())),
                                                    scope: NameScopeDesc::Local,
                                                    kind: None,
                                                },
                                                StrPosition::span_from_range(21..22),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":=".into(), Unquoted)),
                                                    StrPosition::span_from_range(23..25),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("d".into(), Unquoted)),
                                                    StrPosition::span_from_range(26..27),
                                                ),
                                            ],
                                        })),
                                    }],
                                }),
                                StrPosition::span_from_range(20..28),
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
                                                    expr: Some(NotationExpr::Ident("b".into())),
                                                    scope: NameScopeDesc::Local,
                                                    kind: None,
                                                },
                                                StrPosition::span_from_range(30..31),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":=".into(), Unquoted)),
                                                    StrPosition::span_from_range(32..34),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("c".into(), Unquoted)),
                                                    StrPosition::span_from_range(35..36),
                                                ),
                                            ],
                                        })),
                                    }],
                                }),
                                StrPosition::span_from_range(29..37),
                            ),
                            WithSpan::new(
                                Token(Ident("b".into(), Unquoted)),
                                StrPosition::span_from_range(38..39),
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
                                expr: Some(NotationExpr::Ident("a".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '[',
                                    vec![
                                        WithSpan::new(
                                            Token(Ident("b".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::span_from_range(22..23),
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
                                                                    expr: Some(
                                                                        NotationExpr::Ident(
                                                                            "d".into(),
                                                                        ),
                                                                    ),
                                                                    scope: NameScopeDesc::Local,
                                                                    kind: None,
                                                                },
                                                                StrPosition::span_from_range(
                                                                    25..26,
                                                                ),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":=".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::span_from_range(
                                                                        27..29,
                                                                    ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "e".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::span_from_range(
                                                                        30..31,
                                                                    ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            }),
                                            StrPosition::span_from_range(24..32),
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
                                                                    expr: Some(
                                                                        NotationExpr::Ident(
                                                                            "c".into(),
                                                                        ),
                                                                    ),
                                                                    scope: NameScopeDesc::Local,
                                                                    kind: None,
                                                                },
                                                                StrPosition::span_from_range(
                                                                    34..35,
                                                                ),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":=".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::span_from_range(
                                                                        36..38,
                                                                    ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "d".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::span_from_range(
                                                                        39..40,
                                                                    ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            }),
                                            StrPosition::span_from_range(33..41),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("c".into(), Unquoted)),
                                            StrPosition::span_from_range(42..43),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::span_from_range(43..44),
                                        ),
                                        WithSpan::new(
                                            Paren(
                                                '[',
                                                vec![WithSpan::new(
                                                    Token(Ident("f".into(), Unquoted)),
                                                    StrPosition::span_from_range(46..47),
                                                )],
                                            ),
                                            StrPosition::span_from_range(45..48),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..49),
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
                                expr: Some(NotationExpr::Ident("b".into())),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(16..17),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(18..19),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(20..21),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..22),
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
                                expr: Some(NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params: Vec::new(),
                                    target_expr: WithSpan::new(
                                        NotationExpr::Param(-1),
                                        StrPosition::span_from_range(27..28),
                                    ),
                                }))),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(23..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
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
                                expr: Some(NotationExpr::Ident("b".into())),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(16..17),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(18..19),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(20..21),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..22),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("a".into()),
                                        StrPosition::span_from_range(23..24),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Mapping(Box::new(
                                                    MappingNotationExpr {
                                                        kind: &TestInfixMapping,
                                                        params: Vec::new(),
                                                        target_expr: WithSpan::new(
                                                            NotationExpr::Param(-1),
                                                            StrPosition::span_from_range(32..33),
                                                        ),
                                                    },
                                                )),
                                                StrPosition::span_from_range(25..33),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(24..34),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(23..34),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(35..36),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(37..38),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(24..25),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(26..27),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(25..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(24..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..33),
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
                                expr: Some(NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params: vec![WithSpan::new(
                                        (),
                                        StrPosition::span_from_range(37..38),
                                    )],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Param(-2),
                                        StrPosition::span_from_range(40..44),
                                    ),
                                }))),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(34..44),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(45..46),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(47..48),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(24..25),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(26..27),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(25..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(24..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..33),
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
                                expr: Some(NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params: vec![WithSpan::new(
                                        (),
                                        StrPosition::span_from_range(37..38),
                                    )],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Param(-2),
                                        StrPosition::span_from_range(44..48),
                                    ),
                                }))),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(34..48),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(49..50),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(51..52),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(24..25),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(26..27),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(25..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(24..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..33),
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
                                expr: Some(NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params: vec![WithSpan::new(
                                        (),
                                        StrPosition::span_from_range(37..38),
                                    )],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Param(-2),
                                        StrPosition::span_from_range(40..44),
                                    ),
                                }))),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(34..44),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(45..46),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(47..48),
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
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(17..18),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(19..20),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::span_from_range(21..22),
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
                                                expr: Some(NotationExpr::Ident("d".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(24..25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(26..27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::span_from_range(28..29),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::span_from_range(16..30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(31..32),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Param(-2),
                                                    StrPosition::span_from_range(33..34),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(35..36),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(32..37),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(31..37),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(38..39),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(40..41),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..42),
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
                                expr: Some(NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        WithSpan::new((), StrPosition::span_from_range(46..47)),
                                        WithSpan::new((), StrPosition::span_from_range(48..49)),
                                    ],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Param(-3),
                                        StrPosition::span_from_range(51..57),
                                    ),
                                }))),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(43..57),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(58..59),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(60..61),
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
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(17..18),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(19..20),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::span_from_range(21..22),
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
                                                expr: Some(NotationExpr::Ident("d".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(24..25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(26..27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::span_from_range(28..29),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::span_from_range(16..30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(31..32),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Param(-2),
                                                    StrPosition::span_from_range(33..34),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(35..36),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(32..37),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(31..37),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(38..39),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(40..41),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..42),
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
                                expr: Some(NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params: vec![WithSpan::new(
                                        (),
                                        StrPosition::span_from_range(46..47),
                                    )],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                            kind: &TestPrefixMapping,
                                            params: vec![WithSpan::new(
                                                (),
                                                StrPosition::span_from_range(52..53),
                                            )],
                                            target_expr: WithSpan::new(
                                                NotationExpr::Param(-3),
                                                StrPosition::span_from_range(55..61),
                                            ),
                                        })),
                                        StrPosition::span_from_range(49..61),
                                    ),
                                }))),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(43..61),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(62..63),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(64..65),
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
                                                    expr: Some(NotationExpr::Ident("c".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(17..18),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(19..20),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("C".into(), Unquoted)),
                                                    StrPosition::span_from_range(21..22),
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
                                                    expr: Some(NotationExpr::Ident("d".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(24..25),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(26..27),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("D".into(), Unquoted)),
                                                    StrPosition::span_from_range(28..29),
                                                ),
                                            ],
                                        })),
                                    },
                                ],
                            },
                            StrPosition::span_from_range(16..30),
                        )],
                        prefixes: Vec::new(),
                        data: Some(SectionItem::ParamGroup(ParamGroup {
                            param_notations: vec![WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Seq(vec![
                                        WithSpan::new(
                                            NotationExpr::Ident("b".into()),
                                            StrPosition::span_from_range(31..32),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::Paren(
                                                '(',
                                                vec![vec![
                                                    WithSpan::new(
                                                        NotationExpr::Param(-2),
                                                        StrPosition::span_from_range(33..34),
                                                    ),
                                                    WithSpan::new(
                                                        NotationExpr::Param(-1),
                                                        StrPosition::span_from_range(35..36),
                                                    ),
                                                ]],
                                            ),
                                            StrPosition::span_from_range(32..37),
                                        ),
                                    ])),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(31..37),
                            )],
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(38..39),
                                ),
                                WithSpan::new(
                                    Token(Ident("B".into(), Unquoted)),
                                    StrPosition::span_from_range(40..41),
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
                                                expr: Some(NotationExpr::Ident("d".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(44..45),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(46..47),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::span_from_range(48..49),
                                            ),
                                        ],
                                    })),
                                }],
                            },
                            StrPosition::span_from_range(43..50),
                        )],
                        prefixes: Vec::new(),
                        data: Some(SectionItem::ParamGroup(ParamGroup {
                            param_notations: vec![WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Seq(vec![
                                        WithSpan::new(
                                            NotationExpr::Ident("e".into()),
                                            StrPosition::span_from_range(51..52),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::Paren(
                                                '(',
                                                vec![vec![WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(53..54),
                                                )]],
                                            ),
                                            StrPosition::span_from_range(52..55),
                                        ),
                                    ])),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(51..55),
                            )],
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(56..57),
                                ),
                                WithSpan::new(
                                    Token(Ident("E".into(), Unquoted)),
                                    StrPosition::span_from_range(58..59),
                                ),
                            ],
                        })),
                    },
                ],
            },
            StrPosition::span_from_range(15..60),
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
                                expr: Some(NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestPrefixMapping,
                                    params: vec![WithSpan::new(
                                        (),
                                        StrPosition::span_from_range(64..65),
                                    )],
                                    // Make sure that b(-2,-1) is not misidentified as b(c,d).
                                    target_expr: WithSpan::new(
                                        NotationExpr::Seq(vec![
                                            WithSpan::new(
                                                NotationExpr::Ident("b".into()),
                                                StrPosition::span_from_range(67..68),
                                            ),
                                            WithSpan::new(
                                                NotationExpr::Paren(
                                                    '(',
                                                    vec![vec![
                                                        WithSpan::new(
                                                            NotationExpr::Param(-2),
                                                            StrPosition::span_from_range(69..73),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::Param(-1),
                                                            StrPosition::span_from_range(74..75),
                                                        ),
                                                    ]],
                                                ),
                                                StrPosition::span_from_range(68..76),
                                            ),
                                        ]),
                                        StrPosition::span_from_range(67..76),
                                    ),
                                }))),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(61..76),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(77..78),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(79..80),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(24..25),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(26..27),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(25..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(24..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..33),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("a".into()),
                                        StrPosition::span_from_range(34..35),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Mapping(Box::new(
                                                    MappingNotationExpr {
                                                        kind: &TestInfixMapping,
                                                        params: vec![WithSpan::new(
                                                            (),
                                                            StrPosition::span_from_range(36..37),
                                                        )],
                                                        target_expr: WithSpan::new(
                                                            NotationExpr::Param(-2),
                                                            StrPosition::span_from_range(42..46),
                                                        ),
                                                    },
                                                )),
                                                StrPosition::span_from_range(36..46),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(35..47),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(34..47),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(48..49),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(50..51),
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
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(17..18),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(19..20),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::span_from_range(21..22),
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
                                                expr: Some(NotationExpr::Ident("d".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(24..25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(26..27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::span_from_range(28..29),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::span_from_range(16..30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(31..32),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Param(-2),
                                                    StrPosition::span_from_range(33..34),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(35..36),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(32..37),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(31..37),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(38..39),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(40..41),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..42),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("a".into()),
                                        StrPosition::span_from_range(43..44),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Mapping(Box::new(
                                                    MappingNotationExpr {
                                                        kind: &TestInfixMapping,
                                                        params: vec![
                                                            WithSpan::new(
                                                                (),
                                                                StrPosition::span_from_range(
                                                                    46..47,
                                                                ),
                                                            ),
                                                            WithSpan::new(
                                                                (),
                                                                StrPosition::span_from_range(
                                                                    48..49,
                                                                ),
                                                            ),
                                                        ],
                                                        target_expr: WithSpan::new(
                                                            NotationExpr::Param(-3),
                                                            StrPosition::span_from_range(55..61),
                                                        ),
                                                    },
                                                )),
                                                StrPosition::span_from_range(45..61),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(44..62),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(43..62),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(63..64),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(65..66),
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
                                                expr: Some(NotationExpr::Ident("c".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(17..18),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(19..20),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("C".into(), Unquoted)),
                                                StrPosition::span_from_range(21..22),
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
                                                expr: Some(NotationExpr::Ident("d".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(24..25),
                                        )],
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(26..27),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("D".into(), Unquoted)),
                                                StrPosition::span_from_range(28..29),
                                            ),
                                        ],
                                    })),
                                },
                            ],
                        },
                        StrPosition::span_from_range(16..30),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(31..32),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Param(-2),
                                                    StrPosition::span_from_range(33..34),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(35..36),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(32..37),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(31..37),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(38..39),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(40..41),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..42),
        )];
        let param_notations = vec![WithSpan::new(
            Notation {
                expr: Some(NotationExpr::Seq(vec![
                    WithSpan::new(
                        NotationExpr::Ident("a".into()),
                        StrPosition::span_from_range(43..44),
                    ),
                    WithSpan::new(
                        NotationExpr::Paren(
                            '(',
                            vec![vec![WithSpan::new(
                                NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestInfixMapping,
                                    params: vec![WithSpan::new(
                                        (),
                                        StrPosition::span_from_range(45..46),
                                    )],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                            kind: &TestInfixMapping,
                                            params: vec![WithSpan::new(
                                                (),
                                                StrPosition::span_from_range(51..52),
                                            )],
                                            target_expr: WithSpan::new(
                                                NotationExpr::Param(-3),
                                                StrPosition::span_from_range(57..63),
                                            ),
                                        })),
                                        StrPosition::span_from_range(51..63),
                                    ),
                                })),
                                StrPosition::span_from_range(45..63),
                            )]],
                        ),
                        StrPosition::span_from_range(44..64),
                    ),
                ])),
                scope: NameScopeDesc::Global,
                kind: Some(NameKindDesc::Function),
            },
            StrPosition::span_from_range(43..64),
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
                        param_notations,
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(65..66),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(67..68),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
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
                                                        expr: Some(NotationExpr::Ident("d".into())),
                                                        scope: NameScopeDesc::Param,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(27..28),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::span_from_range(29..30),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("D".into(), Unquoted)),
                                                        StrPosition::span_from_range(31..32),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    StrPosition::span_from_range(26..33),
                                )],
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Seq(vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("b".into()),
                                                    StrPosition::span_from_range(34..35),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Paren(
                                                        '(',
                                                        vec![vec![
                                                            WithSpan::new(
                                                                NotationExpr::Param(-2),
                                                                StrPosition::span_from_range(
                                                                    36..37,
                                                                ),
                                                            ),
                                                            WithSpan::new(
                                                                NotationExpr::Param(-1),
                                                                StrPosition::span_from_range(
                                                                    38..39,
                                                                ),
                                                            ),
                                                        ]],
                                                    ),
                                                    StrPosition::span_from_range(35..40),
                                                ),
                                            ])),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Function),
                                        },
                                        StrPosition::span_from_range(34..40),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(41..42),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(43..44),
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
                                            expr: Some(NotationExpr::Seq(vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("e".into()),
                                                    StrPosition::span_from_range(46..47),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Paren(
                                                        '(',
                                                        vec![vec![WithSpan::new(
                                                            NotationExpr::Param(-1),
                                                            StrPosition::span_from_range(48..49),
                                                        )]],
                                                    ),
                                                    StrPosition::span_from_range(47..50),
                                                ),
                                            ])),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Function),
                                        },
                                        StrPosition::span_from_range(46..50),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(51..52),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::span_from_range(53..54),
                                        ),
                                    ],
                                })),
                            },
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..58),
        )];
        let param_notations = vec![WithSpan::new(
            Notation {
                expr: Some(NotationExpr::Seq(vec![
                    WithSpan::new(
                        NotationExpr::Ident("a".into()),
                        StrPosition::span_from_range(59..60),
                    ),
                    WithSpan::new(
                        NotationExpr::Paren(
                            '(',
                            vec![vec![WithSpan::new(
                                NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestInfixMapping,
                                    params: vec![WithSpan::new(
                                        (),
                                        StrPosition::span_from_range(61..62),
                                    )],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Mapping(Box::new(
                                                        MappingNotationExpr {
                                                            kind: &TestInfixMapping,
                                                            params: vec![WithSpan::new(
                                                                (),
                                                                StrPosition::span_from_range(
                                                                    68..69,
                                                                ),
                                                            )],
                                                            target_expr: WithSpan::new(
                                                                NotationExpr::Param(-4),
                                                                StrPosition::span_from_range(
                                                                    74..80,
                                                                ),
                                                            ),
                                                        },
                                                    )),
                                                    StrPosition::span_from_range(68..80),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Param(-2),
                                                    StrPosition::span_from_range(82..86),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(67..87),
                                    ),
                                })),
                                StrPosition::span_from_range(61..87),
                            )]],
                        ),
                        StrPosition::span_from_range(60..88),
                    ),
                ])),
                scope: NameScopeDesc::Global,
                kind: Some(NameKindDesc::Function),
            },
            StrPosition::span_from_range(59..88),
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
                        param_notations,
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(89..90),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(91..92),
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
                                            expr: Some(NotationExpr::Ident("d".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("D".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![
                            WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Seq(vec![
                                        WithSpan::new(
                                            NotationExpr::Ident("b".into()),
                                            StrPosition::span_from_range(24..25),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::Paren(
                                                '(',
                                                vec![vec![WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(26..27),
                                                )]],
                                            ),
                                            StrPosition::span_from_range(25..28),
                                        ),
                                    ])),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(24..28),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Seq(vec![
                                        WithSpan::new(
                                            NotationExpr::Ident("c".into()),
                                            StrPosition::span_from_range(29..30),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::Paren(
                                                '(',
                                                vec![vec![WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(31..32),
                                                )]],
                                            ),
                                            StrPosition::span_from_range(30..33),
                                        ),
                                    ])),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(29..33),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(34..35),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(36..37),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..38),
        )];
        let param_notations = vec![WithSpan::new(
            Notation {
                expr: Some(NotationExpr::Seq(vec![
                    WithSpan::new(
                        NotationExpr::Ident("a".into()),
                        StrPosition::span_from_range(39..40),
                    ),
                    WithSpan::new(
                        NotationExpr::Paren(
                            '(',
                            vec![vec![
                                WithSpan::new(
                                    NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                        kind: &TestInfixMapping,
                                        params: vec![WithSpan::new(
                                            (),
                                            StrPosition::span_from_range(41..42),
                                        )],
                                        target_expr: WithSpan::new(
                                            NotationExpr::Param(-3),
                                            StrPosition::span_from_range(47..51),
                                        ),
                                    })),
                                    StrPosition::span_from_range(41..51),
                                ),
                                WithSpan::new(
                                    NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                        kind: &TestInfixMapping,
                                        params: vec![WithSpan::new(
                                            (),
                                            StrPosition::span_from_range(53..54),
                                        )],
                                        target_expr: WithSpan::new(
                                            NotationExpr::Param(-2),
                                            StrPosition::span_from_range(59..63),
                                        ),
                                    })),
                                    StrPosition::span_from_range(53..63),
                                ),
                            ]],
                        ),
                        StrPosition::span_from_range(40..64),
                    ),
                ])),
                scope: NameScopeDesc::Global,
                kind: Some(NameKindDesc::Function),
            },
            StrPosition::span_from_range(39..64),
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
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
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
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
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
                        param_notations,
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(65..66),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(67..68),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(24..25),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(26..27),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(25..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(24..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..33),
        )];
        let param_notations = vec![WithSpan::new(
            Notation {
                expr: Some(NotationExpr::Seq(vec![
                    WithSpan::new(
                        NotationExpr::Ident("a".into()),
                        StrPosition::span_from_range(34..35),
                    ),
                    WithSpan::new(
                        NotationExpr::Paren(
                            '(',
                            vec![vec![WithSpan::new(
                                NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestInfixMapping,
                                    params: vec![WithSpan::new(
                                        (),
                                        StrPosition::span_from_range(36..37),
                                    )],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Seq(vec![
                                            WithSpan::new(
                                                NotationExpr::Ident("b".into()),
                                                StrPosition::span_from_range(42..43),
                                            ),
                                            WithSpan::new(
                                                NotationExpr::Paren(
                                                    '(',
                                                    vec![vec![WithSpan::new(
                                                        NotationExpr::Ident("x".into()),
                                                        StrPosition::span_from_range(44..45),
                                                    )]],
                                                ),
                                                StrPosition::span_from_range(43..46),
                                            ),
                                        ]),
                                        StrPosition::span_from_range(42..46),
                                    ),
                                })),
                                StrPosition::span_from_range(36..46),
                            )]],
                        ),
                        StrPosition::span_from_range(35..47),
                    ),
                ])),
                scope: NameScopeDesc::Global,
                kind: Some(NameKindDesc::Function),
            },
            StrPosition::span_from_range(34..47),
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
                        param_notations,
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(48..49),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(50..51),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(24..25),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(26..27),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(25..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(24..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..33),
        )];
        let param_notations = vec![WithSpan::new(
            Notation {
                expr: Some(NotationExpr::Seq(vec![
                    WithSpan::new(
                        NotationExpr::Ident("a".into()),
                        StrPosition::span_from_range(34..35),
                    ),
                    WithSpan::new(
                        NotationExpr::Paren(
                            '(',
                            vec![vec![WithSpan::new(
                                NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestInfixMapping,
                                    params: vec![
                                        WithSpan::new((), StrPosition::span_from_range(37..38)),
                                        WithSpan::new((), StrPosition::span_from_range(39..40)),
                                    ],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Seq(vec![
                                            WithSpan::new(
                                                NotationExpr::Ident("b".into()),
                                                StrPosition::span_from_range(46..47),
                                            ),
                                            WithSpan::new(
                                                NotationExpr::Paren(
                                                    '(',
                                                    vec![vec![WithSpan::new(
                                                        NotationExpr::Param(-2),
                                                        StrPosition::span_from_range(48..49),
                                                    )]],
                                                ),
                                                StrPosition::span_from_range(47..50),
                                            ),
                                        ]),
                                        StrPosition::span_from_range(46..50),
                                    ),
                                })),
                                StrPosition::span_from_range(36..50),
                            )]],
                        ),
                        StrPosition::span_from_range(35..51),
                    ),
                ])),
                scope: NameScopeDesc::Global,
                kind: Some(NameKindDesc::Function),
            },
            StrPosition::span_from_range(34..51),
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
                        param_notations,
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(52..53),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(54..55),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(24..25),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(26..27),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(25..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(24..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..33),
        )];
        let param_notations = vec![WithSpan::new(
            Notation {
                expr: Some(NotationExpr::Seq(vec![
                    WithSpan::new(
                        NotationExpr::Ident("a".into()),
                        StrPosition::span_from_range(34..35),
                    ),
                    WithSpan::new(
                        NotationExpr::Paren(
                            '(',
                            vec![vec![WithSpan::new(
                                NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                    kind: &TestInfixMapping,
                                    params: vec![
                                        WithSpan::new((), StrPosition::span_from_range(37..38)),
                                        WithSpan::new((), StrPosition::span_from_range(39..40)),
                                    ],
                                    target_expr: WithSpan::new(
                                        NotationExpr::Seq(vec![
                                            WithSpan::new(
                                                NotationExpr::Ident("b".into()),
                                                StrPosition::span_from_range(46..47),
                                            ),
                                            WithSpan::new(
                                                NotationExpr::Paren(
                                                    '(',
                                                    vec![vec![WithSpan::new(
                                                        NotationExpr::Param(-1),
                                                        StrPosition::span_from_range(48..49),
                                                    )]],
                                                ),
                                                StrPosition::span_from_range(47..50),
                                            ),
                                        ]),
                                        StrPosition::span_from_range(46..50),
                                    ),
                                })),
                                StrPosition::span_from_range(36..50),
                            )]],
                        ),
                        StrPosition::span_from_range(35..51),
                    ),
                ])),
                scope: NameScopeDesc::Global,
                kind: Some(NameKindDesc::Function),
            },
            StrPosition::span_from_range(34..51),
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
                                StrPosition::span_from_range(52..53),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(54..55),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(24..25),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(26..27),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(25..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(24..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..33),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("a".into()),
                                        StrPosition::span_from_range(34..35),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Mapping(Box::new(
                                                    MappingNotationExpr {
                                                        kind: &TestInfixMapping,
                                                        params: vec![WithSpan::new(
                                                            (),
                                                            StrPosition::span_from_range(36..37),
                                                        )],
                                                        target_expr: WithSpan::new(
                                                            NotationExpr::Param(-2),
                                                            StrPosition::span_from_range(42..46),
                                                        ),
                                                    },
                                                )),
                                                StrPosition::span_from_range(36..46),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(35..47),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(34..47),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(48..49),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(50..51),
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
                                            expr: Some(NotationExpr::Ident("c".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(17..18),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(19..20),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("C".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..23),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("b".into()),
                                        StrPosition::span_from_range(24..25),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Param(-1),
                                                StrPosition::span_from_range(26..27),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(25..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(24..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..33),
        )];
        let param_notations = vec![WithSpan::new(
            Notation {
                expr: Some(NotationExpr::Seq(vec![
                    WithSpan::new(
                        NotationExpr::Ident("a".into()),
                        StrPosition::span_from_range(34..35),
                    ),
                    WithSpan::new(
                        NotationExpr::Paren(
                            '(',
                            vec![vec![
                                WithSpan::new(
                                    NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                        kind: &TestInfixMapping,
                                        params: vec![WithSpan::new(
                                            (),
                                            StrPosition::span_from_range(36..37),
                                        )],
                                        target_expr: WithSpan::new(
                                            NotationExpr::Param(-2),
                                            StrPosition::span_from_range(42..46),
                                        ),
                                    })),
                                    StrPosition::span_from_range(36..46),
                                ),
                                WithSpan::new(
                                    NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                        kind: &TestInfixMapping,
                                        params: vec![WithSpan::new(
                                            (),
                                            StrPosition::span_from_range(48..49),
                                        )],
                                        target_expr: WithSpan::new(
                                            NotationExpr::Param(-2),
                                            StrPosition::span_from_range(54..58),
                                        ),
                                    })),
                                    StrPosition::span_from_range(48..58),
                                ),
                            ]],
                        ),
                        StrPosition::span_from_range(35..59),
                    ),
                ])),
                scope: NameScopeDesc::Global,
                kind: Some(NameKindDesc::Function),
            },
            StrPosition::span_from_range(34..59),
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
                        param_notations,
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(60..61),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(62..63),
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
                                                        expr: Some(NotationExpr::Ident("e".into())),
                                                        scope: NameScopeDesc::Param,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(18..19),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::span_from_range(20..21),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("E".into(), Unquoted)),
                                                        StrPosition::span_from_range(22..23),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    StrPosition::span_from_range(17..24),
                                )],
                                prefixes: Vec::new(),
                                data: Some(SectionItem::ParamGroup(ParamGroup {
                                    param_notations: vec![WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Seq(vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("d".into()),
                                                    StrPosition::span_from_range(25..26),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Paren(
                                                        '(',
                                                        vec![vec![WithSpan::new(
                                                            NotationExpr::Param(-1),
                                                            StrPosition::span_from_range(27..28),
                                                        )]],
                                                    ),
                                                    StrPosition::span_from_range(26..29),
                                                ),
                                            ])),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Function),
                                        },
                                        StrPosition::span_from_range(25..29),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(30..31),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("D".into(), Unquoted)),
                                            StrPosition::span_from_range(32..33),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(16..34),
                    )],
                    prefixes: Vec::new(),
                    data: Some(SectionItem::ParamGroup(ParamGroup {
                        param_notations: vec![
                            WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Seq(vec![
                                        WithSpan::new(
                                            NotationExpr::Ident("b".into()),
                                            StrPosition::span_from_range(35..36),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::Paren(
                                                '(',
                                                vec![vec![WithSpan::new(
                                                    NotationExpr::Mapping(Box::new(
                                                        MappingNotationExpr {
                                                            kind: &TestInfixMapping,
                                                            params: vec![WithSpan::new(
                                                                (),
                                                                StrPosition::span_from_range(
                                                                    37..38,
                                                                ),
                                                            )],
                                                            target_expr: WithSpan::new(
                                                                NotationExpr::Param(-2),
                                                                StrPosition::span_from_range(
                                                                    43..47,
                                                                ),
                                                            ),
                                                        },
                                                    )),
                                                    StrPosition::span_from_range(37..47),
                                                )]],
                                            ),
                                            StrPosition::span_from_range(36..48),
                                        ),
                                    ])),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(35..48),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Seq(vec![
                                        WithSpan::new(
                                            NotationExpr::Ident("c".into()),
                                            StrPosition::span_from_range(49..50),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::Paren(
                                                '(',
                                                vec![vec![WithSpan::new(
                                                    NotationExpr::Mapping(Box::new(
                                                        MappingNotationExpr {
                                                            kind: &TestPrefixMapping,
                                                            params: vec![WithSpan::new(
                                                                (),
                                                                StrPosition::span_from_range(
                                                                    54..55,
                                                                ),
                                                            )],
                                                            target_expr: WithSpan::new(
                                                                NotationExpr::Param(-2),
                                                                StrPosition::span_from_range(
                                                                    57..61,
                                                                ),
                                                            ),
                                                        },
                                                    )),
                                                    StrPosition::span_from_range(51..61),
                                                )]],
                                            ),
                                            StrPosition::span_from_range(50..62),
                                        ),
                                    ])),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(49..62),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(63..64),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(65..66),
                            ),
                        ],
                    })),
                }],
            },
            StrPosition::span_from_range(15..67),
        )];
        let param_notations = vec![WithSpan::new(
            Notation {
                expr: Some(NotationExpr::Seq(vec![
                    WithSpan::new(
                        NotationExpr::Ident("a".into()),
                        StrPosition::span_from_range(68..69),
                    ),
                    WithSpan::new(
                        NotationExpr::Paren(
                            '(',
                            vec![vec![
                                WithSpan::new(
                                    NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                        kind: &TestInfixMapping,
                                        params: vec![WithSpan::new(
                                            (),
                                            StrPosition::span_from_range(77..81),
                                        )],
                                        target_expr: WithSpan::new(
                                            NotationExpr::Param(-3),
                                            StrPosition::span_from_range(87..100),
                                        ),
                                    })),
                                    StrPosition::span_from_range(70..100),
                                ),
                                WithSpan::new(
                                    NotationExpr::Mapping(Box::new(MappingNotationExpr {
                                        kind: &TestPrefixMapping,
                                        params: vec![WithSpan::new(
                                            (),
                                            StrPosition::span_from_range(111..115),
                                        )],
                                        target_expr: WithSpan::new(
                                            NotationExpr::Param(-2),
                                            StrPosition::span_from_range(117..130),
                                        ),
                                    })),
                                    StrPosition::span_from_range(102..130),
                                ),
                            ]],
                        ),
                        StrPosition::span_from_range(69..131),
                    ),
                ])),
                scope: NameScopeDesc::Global,
                kind: Some(NameKindDesc::Function),
            },
            StrPosition::span_from_range(68..131),
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
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Function)),
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
                                SpanDesc::NameRef(
                                    NameScopeDesc::Param,
                                    Some(NameKindDesc::Function),
                                ),
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
                        param_notations,
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(132..133),
                            ),
                            WithSpan::new(
                                Token(Ident("A".into(), Unquoted)),
                                StrPosition::span_from_range(134..135),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(17..18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(17..18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(17..18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
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
                                expr: Some(NotationExpr::Ident("y".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(24..25),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(26..27),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(28..29),
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
                                expr: Some(NotationExpr::Ident("x".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(17..18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
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
                                expr: Some(NotationExpr::Ident("y".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(26..27),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(28..29),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(30..31),
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
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                                                expr: Some(NotationExpr::Ident("a".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(16..17),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("b".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(18..19),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(22..23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..24),
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
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("x".into()),
                                        StrPosition::span_from_range(27..28),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::ReservedChar('_'),
                                        StrPosition::span_from_range(28..29),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Param(-2),
                                        StrPosition::span_from_range(29..30),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(27..30),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(33..34),
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
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                                        StrPosition::span_from_range(37..38),
                                    )],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(36..39),
                    )],
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("y".into()),
                                        StrPosition::span_from_range(40..41),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::ReservedChar('_'),
                                        StrPosition::span_from_range(41..42),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Param(-2),
                                        StrPosition::span_from_range(42..43),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::ReservedChar('_'),
                                        StrPosition::span_from_range(43..44),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Param(-1),
                                        StrPosition::span_from_range(44..45),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::ReservedChar('_'),
                                        StrPosition::span_from_range(45..46),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("c".into()),
                                        StrPosition::span_from_range(46..47),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(40..47),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(48..49),
                            ),
                            WithSpan::new(
                                Token(Ident("V".into(), Unquoted)),
                                StrPosition::span_from_range(50..51),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("z".into()),
                                        StrPosition::span_from_range(55..56),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::ReservedChar('_'),
                                        StrPosition::span_from_range(56..57),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("a".into()),
                                        StrPosition::span_from_range(57..58),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(55..58),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(59..60),
                            ),
                            WithSpan::new(
                                Token(Ident("W".into(), Unquoted)),
                                StrPosition::span_from_range(61..62),
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
                                                        expr: Some(NotationExpr::Ident("a".into())),
                                                        scope: NameScopeDesc::Param,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(17..18),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::span_from_range(19..20),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("T".into(), Unquoted)),
                                                        StrPosition::span_from_range(21..22),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    StrPosition::span_from_range(16..23),
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
                                                    expr: Some(NotationExpr::Seq(vec![
                                                        WithSpan::new(
                                                            NotationExpr::Ident("b".into()),
                                                            StrPosition::span_from_range(26..27),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::ReservedChar('_'),
                                                            StrPosition::span_from_range(27..28),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::Param(-1),
                                                            StrPosition::span_from_range(28..29),
                                                        ),
                                                    ])),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Function),
                                                },
                                                StrPosition::span_from_range(26..29),
                                            )],
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(30..31),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("U".into(), Unquoted)),
                                                    StrPosition::span_from_range(32..33),
                                                ),
                                            ],
                                        })),
                                    }],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..37),
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
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("c".into()),
                                        StrPosition::span_from_range(40..41),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Mapping(Box::new(
                                                    MappingNotationExpr {
                                                        kind: &TestInfixMapping,
                                                        params: vec![WithSpan::new(
                                                            (),
                                                            StrPosition::span_from_range(42..43),
                                                        )],
                                                        target_expr: WithSpan::new(
                                                            NotationExpr::Param(-2),
                                                            StrPosition::span_from_range(48..51),
                                                        ),
                                                    },
                                                )),
                                                StrPosition::span_from_range(42..51),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(41..52),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(40..52),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(53..54),
                            ),
                            WithSpan::new(
                                Token(Ident("V".into(), Unquoted)),
                                StrPosition::span_from_range(55..56),
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
                        StrPosition::span_from_range(15..16),
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
                        StrPosition::span_from_range(15..16),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("y".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(17..18),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(19..20),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
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
                            StrPosition::span_from_range(15..16),
                        ),
                        WithSpan::new(
                            NotationExpr::Ident("y".into()),
                            StrPosition::span_from_range(17..18),
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
                        StrPosition::span_from_range(15..16),
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
                                expr: Some(NotationExpr::Ident("y".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(19..20),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(21..22),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(23..24),
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
                        StrPosition::span_from_range(15..16),
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
                        StrPosition::span_from_range(19..20),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("z".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(21..22),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(23..24),
                            ),
                            WithSpan::new(
                                Token(Ident("T".into(), Unquoted)),
                                StrPosition::span_from_range(25..26),
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
                            WithSpan::new(
                                NotationExpr::Ident("x".into()),
                                StrPosition::span_from_range(16..17),
                            ),
                            WithSpan::new(
                                NotationExpr::Ident("y".into()),
                                StrPosition::span_from_range(18..19),
                            ),
                            WithSpan::new(
                                NotationExpr::Ident("z".into()),
                                StrPosition::span_from_range(20..21),
                            ),
                        ]),
                        StrPosition::span_from_range(16..21),
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
                                            expr: Some(NotationExpr::Ident("x".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::span_from_range(23..24),
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
                                            expr: Some(NotationExpr::Seq(vec![
                                                WithSpan::new(
                                                    NotationExpr::Ident("x".into()),
                                                    StrPosition::span_from_range(16..17),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Ident("y".into()),
                                                    StrPosition::span_from_range(18..19),
                                                ),
                                            ])),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..19),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(22..23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..24),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::span_from_range(26..29),
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
                                            expr: Some(NotationExpr::Ident("x".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::span_from_range(23..24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("y".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(25..26),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(27..28),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
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
                                            expr: Some(NotationExpr::Ident("x".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::span_from_range(23..24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("y".into())),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(26..27),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
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
                                            expr: Some(NotationExpr::Ident("x".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::span_from_range(23..24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("y".into()),
                                        StrPosition::span_from_range(26..27),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("z".into()),
                                        StrPosition::span_from_range(28..29),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(26..29),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(33..34),
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
                        SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                                                expr: Some(NotationExpr::Ident("x".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(16..17),
                                        ),
                                        WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("y".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(18..19),
                                        ),
                                    ],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(22..23),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..24),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-2),
                        StrPosition::span_from_range(25..26),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Paren(
                                    '(',
                                    vec![vec![WithSpan::new(
                                        NotationExpr::Param(-1),
                                        StrPosition::span_from_range(28..29),
                                    )]],
                                )),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(27..30),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(33..34),
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
                                            expr: Some(NotationExpr::Ident("x".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::span_from_range(23..24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("y".into()),
                                        StrPosition::span_from_range(25..26),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '(',
                                            vec![vec![WithSpan::new(
                                                NotationExpr::Ident("z".into()),
                                                StrPosition::span_from_range(27..28),
                                            )]],
                                        ),
                                        StrPosition::span_from_range(26..29),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(25..29),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(30..31),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(32..33),
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
                                            expr: Some(NotationExpr::Ident("x".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::span_from_range(23..24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("y".into()),
                                        StrPosition::span_from_range(25..26),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Ident("z".into()),
                                        StrPosition::span_from_range(27..28),
                                    ),
                                ])),
                                scope: NameScopeDesc::Global,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(25..28),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
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
                                SpanDesc::NameDef(
                                    NameScopeDesc::Global,
                                    Some(NameKindDesc::Function),
                                ),
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
                                            expr: Some(NotationExpr::Ident("x".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(16..17),
                                    )],
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(18..19),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("T".into(), Unquoted)),
                                            StrPosition::span_from_range(20..21),
                                        ),
                                    ],
                                })),
                            }],
                        },
                        StrPosition::span_from_range(15..22),
                    )],
                    prefixes: vec![WithSpan::new(
                        NotationExpr::Param(-1),
                        StrPosition::span_from_range(23..24),
                    )],
                    data: Some(ParamGroup {
                        param_notations: vec![
                            WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Ident("y".into())),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(25..26),
                            ),
                            WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Ident("z".into())),
                                    scope: NameScopeDesc::Global,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(27..28),
                            ),
                        ],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                            WithSpan::new(
                                Token(Ident("U".into(), Unquoted)),
                                StrPosition::span_from_range(31..32),
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
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: Vec::new(),
                                }),
                                StrPosition::span_from_range(20..22),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("x".into())),
                                                    scope: NameScopeDesc::Instance,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(21..22),
                                            ),
                                            data: Vec::new(),
                                        },
                                        extra_parts: Vec::new(),
                                    }],
                                }),
                                StrPosition::span_from_range(20..23),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    Input(" || "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("x".into())),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(21..22),
                                                ),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("y".into())),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(26..27),
                                                ),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..28),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    Input(" | | "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("x".into())),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(21..22),
                                                ),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("y".into())),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(27..28),
                                                ),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..29),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    Input(" ||"),
                    WithDiag(
                        Box::new(Input("|")),
                        (Error(Some(SyntaxError)), "superfluous separator".into()),
                    ),
                    Input(" "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("x".into())),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(21..22),
                                                ),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("y".into())),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(27..28),
                                                ),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..29),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    Input(" || "),
                    WithDesc(
                        Box::new(Seq(vec![
                            WithDesc(Box::new(Input("|")), SpanDesc::ParenStart),
                            Input("y"),
                            WithDesc(Box::new(Input("|")), SpanDesc::ParenEnd),
                        ])),
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Paren(
                                                            '|',
                                                            vec![vec![WithSpan::new(
                                                                NotationExpr::Ident("x".into()),
                                                                StrPosition::span_from_range(
                                                                    22..23,
                                                                ),
                                                            )]],
                                                        )),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(21..24),
                                                ),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Paren(
                                                            '|',
                                                            vec![vec![WithSpan::new(
                                                                NotationExpr::Ident("y".into()),
                                                                StrPosition::span_from_range(
                                                                    29..30,
                                                                ),
                                                            )]],
                                                        )),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(28..31),
                                                ),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..32),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Function)),
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
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                            expr: Some(NotationExpr::Ident(
                                                                "y".into(),
                                                            )),
                                                            scope: NameScopeDesc::Field,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::span_from_range(28..29),
                                                    )],
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::span_from_range(30..31),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("T".into(), Unquoted)),
                                                            StrPosition::span_from_range(32..33),
                                                        ),
                                                    ],
                                                })),
                                            }],
                                        },
                                        param: Param {
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Seq(vec![
                                                        WithSpan::new(
                                                            NotationExpr::Ident("x".into()),
                                                            StrPosition::span_from_range(21..22),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::Paren(
                                                                '(',
                                                                vec![vec![WithSpan::new(
                                                                    NotationExpr::Param(-1),
                                                                    StrPosition::span_from_range(
                                                                        23..24,
                                                                    ),
                                                                )]],
                                                            ),
                                                            StrPosition::span_from_range(22..25),
                                                        ),
                                                    ])),
                                                    scope: NameScopeDesc::Instance,
                                                    kind: Some(NameKindDesc::Function),
                                                },
                                                StrPosition::span_from_range(21..25),
                                            ),
                                            data: Vec::new(),
                                        },
                                        extra_parts: Vec::new(),
                                    }],
                                }),
                                StrPosition::span_from_range(20..36),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Function)),
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
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                            expr: Some(NotationExpr::Ident(
                                                                "y".into(),
                                                            )),
                                                            scope: NameScopeDesc::Field,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::span_from_range(28..29),
                                                    )],
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::span_from_range(30..31),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("T".into(), Unquoted)),
                                                            StrPosition::span_from_range(32..33),
                                                        ),
                                                    ],
                                                })),
                                            }],
                                        },
                                        param: Param {
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Seq(vec![
                                                        WithSpan::new(
                                                            NotationExpr::Ident("x".into()),
                                                            StrPosition::span_from_range(21..22),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::Paren(
                                                                '(',
                                                                vec![vec![WithSpan::new(
                                                                    NotationExpr::Param(-1),
                                                                    StrPosition::span_from_range(
                                                                        23..24,
                                                                    ),
                                                                )]],
                                                            ),
                                                            StrPosition::span_from_range(22..25),
                                                        ),
                                                    ])),
                                                    scope: NameScopeDesc::Instance,
                                                    kind: Some(NameKindDesc::Function),
                                                },
                                                StrPosition::span_from_range(21..25),
                                            ),
                                            data: Vec::new(),
                                        },
                                        extra_parts: Vec::new(),
                                    }],
                                }),
                                StrPosition::span_from_range(20..37),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Function)),
                    ),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T || "),
                    WithDesc(
                        Box::new(Input("z")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                                    expr: Some(
                                                                        NotationExpr::Ident(
                                                                            "y".into(),
                                                                        ),
                                                                    ),
                                                                    scope: NameScopeDesc::Field,
                                                                    kind: Some(NameKindDesc::Value),
                                                                },
                                                                StrPosition::span_from_range(
                                                                    28..29,
                                                                ),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::span_from_range(
                                                                        30..31,
                                                                    ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "T".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::span_from_range(
                                                                        32..33,
                                                                    ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            },
                                            param: Param {
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Seq(vec![
                                                            WithSpan::new(
                                                                NotationExpr::Ident("x".into()),
                                                                StrPosition::span_from_range(
                                                                    21..22,
                                                                ),
                                                            ),
                                                            WithSpan::new(
                                                                NotationExpr::Paren(
                                                                    '(',
                                                                    vec![vec![WithSpan::new(
                                                                    NotationExpr::Param(-1),
                                                                    StrPosition::span_from_range(
                                                                        23..24,
                                                                    ),
                                                                )]],
                                                                ),
                                                                StrPosition::span_from_range(
                                                                    22..25,
                                                                ),
                                                            ),
                                                        ])),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Function),
                                                    },
                                                    StrPosition::span_from_range(21..25),
                                                ),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("z".into())),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(37..38),
                                                ),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..39),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Function)),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                                    expr: Some(
                                                                        NotationExpr::Ident(
                                                                            "y".into(),
                                                                        ),
                                                                    ),
                                                                    scope: NameScopeDesc::Field,
                                                                    kind: Some(NameKindDesc::Value),
                                                                },
                                                                StrPosition::span_from_range(
                                                                    28..29,
                                                                ),
                                                            )],
                                                            data: vec![
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        ":".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::span_from_range(
                                                                        30..31,
                                                                    ),
                                                                ),
                                                                WithSpan::new(
                                                                    Token(Ident(
                                                                        "T".into(),
                                                                        Unquoted,
                                                                    )),
                                                                    StrPosition::span_from_range(
                                                                        32..33,
                                                                    ),
                                                                ),
                                                            ],
                                                        },
                                                    )),
                                                }],
                                            },
                                            param: Param {
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Seq(vec![
                                                            WithSpan::new(
                                                                NotationExpr::Ident("x".into()),
                                                                StrPosition::span_from_range(
                                                                    21..22,
                                                                ),
                                                            ),
                                                            WithSpan::new(
                                                                NotationExpr::Paren(
                                                                    '(',
                                                                    vec![vec![WithSpan::new(
                                                                    NotationExpr::Param(-1),
                                                                    StrPosition::span_from_range(
                                                                        23..24,
                                                                    ),
                                                                )]],
                                                                ),
                                                                StrPosition::span_from_range(
                                                                    22..25,
                                                                ),
                                                            ),
                                                        ])),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Function),
                                                    },
                                                    StrPosition::span_from_range(21..25),
                                                ),
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
                                                                StrPosition::span_from_range(
                                                                    36..37,
                                                                ),
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
                                                                StrPosition::span_from_range(
                                                                    40..41,
                                                                ),
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
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("z".into())),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(49..50),
                                                ),
                                                data: Vec::new(),
                                            },
                                            extra_parts: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..51),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Function)),
                    ),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("y")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : T | "),
                    WithDesc(
                        Box::new(Input("z")),
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
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
                                expr: Some(NotationExpr::Ident("T".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                            expr: Some(NotationExpr::Ident(
                                                                "y".into(),
                                                            )),
                                                            scope: NameScopeDesc::Field,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::span_from_range(28..29),
                                                    )],
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::span_from_range(30..31),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("T".into(), Unquoted)),
                                                            StrPosition::span_from_range(32..33),
                                                        ),
                                                    ],
                                                })),
                                            }],
                                        },
                                        param: Param {
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Seq(vec![
                                                        WithSpan::new(
                                                            NotationExpr::Ident("x".into()),
                                                            StrPosition::span_from_range(21..22),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::Paren(
                                                                '(',
                                                                vec![vec![WithSpan::new(
                                                                    NotationExpr::Param(-1),
                                                                    StrPosition::span_from_range(
                                                                        23..24,
                                                                    ),
                                                                )]],
                                                            ),
                                                            StrPosition::span_from_range(22..25),
                                                        ),
                                                    ])),
                                                    scope: NameScopeDesc::Instance,
                                                    kind: Some(NameKindDesc::Function),
                                                },
                                                StrPosition::span_from_range(21..25),
                                            ),
                                            data: Vec::new(),
                                        },
                                        extra_parts: vec![vec![Parameterized {
                                            parameterizations: Vec::new(),
                                            prefixes: Vec::new(),
                                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                                param_notations: vec![WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("z".into())),
                                                        scope: NameScopeDesc::Instance,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(36..37),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":=".into(), Unquoted)),
                                                        StrPosition::span_from_range(38..40),
                                                    ),
                                                    WithSpan::new(
                                                        Mapping(super::Mapping {
                                                            kind: &TestPrefixMapping,
                                                            params: vec![MappingParam {
                                                                mappings: Vec::new(),
                                                                notation: WithSpan::new(
                                                                    Notation {
                                                                        expr: Some(
                                                                            NotationExpr::Ident(
                                                                                "a".into(),
                                                                            ),
                                                                        ),
                                                                        scope: NameScopeDesc::Param,
                                                                        kind: None,
                                                                    },
                                                                    StrPosition::span_from_range(
                                                                        44..45,
                                                                    ),
                                                                ),
                                                                data: Vec::new(),
                                                            }],
                                                        }),
                                                        StrPosition::span_from_range(41..45),
                                                    ),
                                                ],
                                            })),
                                        }]],
                                    }],
                                }),
                                StrPosition::span_from_range(20..46),
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
                                    expr: Some(NotationExpr::Ident("i".into())),
                                    scope: NameScopeDesc::Field,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(33..34),
                            )],
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(35..36),
                                ),
                                WithSpan::new(
                                    Token(Ident("I".into(), Unquoted)),
                                    StrPosition::span_from_range(37..38),
                                ),
                            ],
                        })),
                    }],
                },
                param: Param {
                    notation: WithSpan::new(
                        Notation {
                            expr: Some(NotationExpr::Seq(vec![
                                WithSpan::new(
                                    NotationExpr::Ident("x".into()),
                                    StrPosition::span_from_range(21..22),
                                ),
                                WithSpan::new(
                                    NotationExpr::ReservedChar('_'),
                                    StrPosition::span_from_range(22..23),
                                ),
                                WithSpan::new(
                                    NotationExpr::Param(-1),
                                    StrPosition::span_from_range(23..24),
                                ),
                            ])),
                            scope: NameScopeDesc::Instance,
                            kind: Some(NameKindDesc::Function),
                        },
                        StrPosition::span_from_range(21..24),
                    ),
                    data: vec![
                        WithSpan::new(
                            Token(Ident("↦".into(), Unquoted)),
                            StrPosition::span_from_range(25..28),
                        ),
                        WithSpan::new(
                            Token(Ident("i".into(), Unquoted)),
                            StrPosition::span_from_range(29..30),
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
                                        expr: Some(NotationExpr::Ident("j".into())),
                                        scope: NameScopeDesc::Field,
                                        kind: Some(NameKindDesc::Value),
                                    },
                                    StrPosition::span_from_range(58..59),
                                )],
                                data: vec![
                                    WithSpan::new(
                                        Token(Ident(":".into(), Unquoted)),
                                        StrPosition::span_from_range(60..61),
                                    ),
                                    WithSpan::new(
                                        Token(Ident("J".into(), Unquoted)),
                                        StrPosition::span_from_range(62..63),
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
                                        expr: Some(NotationExpr::Ident("k".into())),
                                        scope: NameScopeDesc::Field,
                                        kind: Some(NameKindDesc::Value),
                                    },
                                    StrPosition::span_from_range(65..66),
                                )],
                                data: vec![
                                    WithSpan::new(
                                        Token(Ident(":".into(), Unquoted)),
                                        StrPosition::span_from_range(67..68),
                                    ),
                                    WithSpan::new(
                                        Token(Ident("K".into(), Unquoted)),
                                        StrPosition::span_from_range(69..70),
                                    ),
                                ],
                            })),
                        },
                    ],
                },
                param: Param {
                    notation: WithSpan::new(
                        Notation {
                            expr: Some(NotationExpr::Seq(vec![
                                WithSpan::new(
                                    NotationExpr::Ident("y".into()),
                                    StrPosition::span_from_range(42..43),
                                ),
                                WithSpan::new(
                                    NotationExpr::ReservedChar('_'),
                                    StrPosition::span_from_range(43..44),
                                ),
                                WithSpan::new(
                                    NotationExpr::Param(-2),
                                    StrPosition::span_from_range(44..45),
                                ),
                                WithSpan::new(
                                    NotationExpr::ReservedChar('_'),
                                    StrPosition::span_from_range(45..46),
                                ),
                                WithSpan::new(
                                    NotationExpr::Param(-1),
                                    StrPosition::span_from_range(46..47),
                                ),
                            ])),
                            scope: NameScopeDesc::Instance,
                            kind: Some(NameKindDesc::Function),
                        },
                        StrPosition::span_from_range(42..47),
                    ),
                    data: vec![
                        WithSpan::new(
                            Token(Ident("↦".into(), Unquoted)),
                            StrPosition::span_from_range(48..51),
                        ),
                        WithSpan::new(
                            Token(Ident("j".into(), Unquoted)),
                            StrPosition::span_from_range(52..53),
                        ),
                        WithSpan::new(
                            Token(Ident("k".into(), Unquoted)),
                            StrPosition::span_from_range(54..55),
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
                                StrPosition::span_from_range(73..74),
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
                                StrPosition::span_from_range(77..78),
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
                notation: WithSpan::new(
                    Notation {
                        expr: Some(NotationExpr::Ident("z".into())),
                        scope: NameScopeDesc::Instance,
                        kind: Some(NameKindDesc::Value),
                    },
                    StrPosition::span_from_range(83..84),
                ),
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
                        SpanDesc::NameRef(NameScopeDesc::Instance, Some(NameKindDesc::Function)),
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
                        SpanDesc::NameRef(NameScopeDesc::Instance, Some(NameKindDesc::Function)),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
                    ),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("c".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: object_items_1,
                                }),
                                StrPosition::span_from_range(20..79),
                            ),
                            WithSpan::new(
                                Token(ReservedChar('|', Isolated, Isolated)),
                                StrPosition::span_from_range(80..81),
                            ),
                            WithSpan::new(
                                Object(super::Object {
                                    kind: &TestMetaModel,
                                    items: object_items_2,
                                }),
                                StrPosition::span_from_range(82..85),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let type_output = ParameterEvent::ParamGroup(Parameterized {
            parameterizations: Vec::new(),
            prefixes: Vec::new(),
            data: Some(ParamGroup {
                param_notations: vec![WithSpan::new(
                    Notation {
                        expr: Some(NotationExpr::Ident("ℕ".into())),
                        scope: NameScopeDesc::Global,
                        kind: None,
                    },
                    StrPosition::span_from_range(15..18),
                )],
                data: vec![
                    WithSpan::new(
                        Token(Ident(":=".into(), Unquoted)),
                        StrPosition::span_from_range(19..21),
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
                                        notation: WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("0".into())),
                                                scope: NameScopeDesc::Instance,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(23..24),
                                        ),
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
                                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                                param_notations: vec![WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("n".into())),
                                                        scope: NameScopeDesc::Field,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(35..36),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::span_from_range(37..38),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("ℕ".into(), Unquoted)),
                                                        StrPosition::span_from_range(39..42),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    param: Param {
                                        notation: WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Seq(vec![
                                                    WithSpan::new(
                                                        NotationExpr::Ident("S".into()),
                                                        StrPosition::span_from_range(28..29),
                                                    ),
                                                    WithSpan::new(
                                                        NotationExpr::Paren(
                                                            '(',
                                                            vec![vec![WithSpan::new(
                                                                NotationExpr::Param(-1),
                                                                StrPosition::span_from_range(
                                                                    30..31,
                                                                ),
                                                            )]],
                                                        ),
                                                        StrPosition::span_from_range(29..32),
                                                    ),
                                                ])),
                                                scope: NameScopeDesc::Instance,
                                                kind: Some(NameKindDesc::Function),
                                            },
                                            StrPosition::span_from_range(28..32),
                                        ),
                                        data: Vec::new(),
                                    },
                                    extra_parts: Vec::new(),
                                },
                            ],
                        }),
                        StrPosition::span_from_range(22..43),
                    ),
                ],
            }),
        });
        let fn_output = ParameterEvent::ParamGroup(Parameterized {
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
                                        expr: Some(NotationExpr::Ident("m".into())),
                                        scope: NameScopeDesc::Param,
                                        kind: Some(NameKindDesc::Value),
                                    },
                                    StrPosition::span_from_range(46..47),
                                ),
                                WithSpan::new(
                                    Notation {
                                        expr: Some(NotationExpr::Ident("n".into())),
                                        scope: NameScopeDesc::Param,
                                        kind: Some(NameKindDesc::Value),
                                    },
                                    StrPosition::span_from_range(48..49),
                                ),
                            ],
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(50..51),
                                ),
                                WithSpan::new(
                                    Token(Ident("ℕ".into(), Unquoted)),
                                    StrPosition::span_from_range(52..55),
                                ),
                            ],
                        })),
                    }],
                },
                StrPosition::span_from_range(45..56),
            )],
            prefixes: Vec::new(),
            data: Some(ParamGroup {
                param_notations: vec![WithSpan::new(
                    Notation {
                        expr: Some(NotationExpr::Seq(vec![
                            WithSpan::new(
                                NotationExpr::Param(-2),
                                StrPosition::span_from_range(57..58),
                            ),
                            WithSpan::new(
                                NotationExpr::Ident("+".into()),
                                StrPosition::span_from_range(59..60),
                            ),
                            WithSpan::new(
                                NotationExpr::Param(-1),
                                StrPosition::span_from_range(61..62),
                            ),
                        ])),
                        scope: NameScopeDesc::Global,
                        kind: Some(NameKindDesc::Function),
                    },
                    StrPosition::span_from_range(57..62),
                )],
                data: vec![
                    WithSpan::new(
                        Token(Ident(":".into(), Unquoted)),
                        StrPosition::span_from_range(63..64),
                    ),
                    WithSpan::new(
                        Token(Ident("ℕ".into(), Unquoted)),
                        StrPosition::span_from_range(65..68),
                    ),
                    WithSpan::new(
                        Token(Ident(":=".into(), Unquoted)),
                        StrPosition::span_from_range(69..71),
                    ),
                    WithSpan::new(
                        Token(Ident("n".into(), Unquoted)),
                        StrPosition::span_from_range(72..73),
                    ),
                    WithSpan::new(
                        Token(ReservedChar('.', StronglyConnected, StronglyConnected)),
                        StrPosition::span_from_range(73..74),
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
                                        notation: WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("0".into())),
                                                scope: NameScopeDesc::Instance,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(75..76),
                                        ),
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident("↦".into(), Unquoted)),
                                                StrPosition::span_from_range(77..80),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("m".into(), Unquoted)),
                                                StrPosition::span_from_range(81..82),
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
                                            data: Some(SectionItem::ParamGroup(ParamGroup {
                                                param_notations: vec![WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("x".into())),
                                                        scope: NameScopeDesc::Field,
                                                        kind: Some(NameKindDesc::Value),
                                                    },
                                                    StrPosition::span_from_range(106..107),
                                                )],
                                                data: vec![
                                                    WithSpan::new(
                                                        Token(Ident(":".into(), Unquoted)),
                                                        StrPosition::span_from_range(108..109),
                                                    ),
                                                    WithSpan::new(
                                                        Token(Ident("ℕ".into(), Unquoted)),
                                                        StrPosition::span_from_range(110..113),
                                                    ),
                                                ],
                                            })),
                                        }],
                                    },
                                    param: Param {
                                        notation: WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Seq(vec![
                                                    WithSpan::new(
                                                        NotationExpr::Ident("S".into()),
                                                        StrPosition::span_from_range(86..87),
                                                    ),
                                                    WithSpan::new(
                                                        NotationExpr::Paren(
                                                            '(',
                                                            vec![vec![WithSpan::new(
                                                                NotationExpr::Param(-1),
                                                                StrPosition::span_from_range(
                                                                    88..89,
                                                                ),
                                                            )]],
                                                        ),
                                                        StrPosition::span_from_range(87..90),
                                                    ),
                                                ])),
                                                scope: NameScopeDesc::Instance,
                                                kind: Some(NameKindDesc::Function),
                                            },
                                            StrPosition::span_from_range(86..90),
                                        ),
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident("↦".into(), Unquoted)),
                                                StrPosition::span_from_range(91..94),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("S".into(), Unquoted)),
                                                StrPosition::span_from_range(95..96),
                                            ),
                                            WithSpan::new(
                                                Paren(
                                                    '(',
                                                    vec![
                                                        WithSpan::new(
                                                            Token(Ident("m".into(), Unquoted)),
                                                            StrPosition::span_from_range(97..98),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("+".into(), Unquoted)),
                                                            StrPosition::span_from_range(99..100),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("x".into(), Unquoted)),
                                                            StrPosition::span_from_range(101..102),
                                                        ),
                                                    ],
                                                ),
                                                StrPosition::span_from_range(96..103),
                                            ),
                                        ],
                                    },
                                    extra_parts: Vec::new(),
                                },
                            ],
                        }),
                        StrPosition::span_from_range(74..114),
                    ),
                ],
            }),
        });
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
                            SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
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
                        SpanDesc::NameDef(NameScopeDesc::Instance, Some(NameKindDesc::Function)),
                    ),
                    Input(" | "),
                    WithDesc(
                        Box::new(Input("n")),
                        SpanDesc::NameDef(NameScopeDesc::Field, Some(NameKindDesc::Value)),
                    ),
                    Input(" : ℕ"),
                    WithDesc(Box::new(Input("}")), SpanDesc::ParenEnd),
                ]),
                Some(type_output),
            ),
            (Input("; "), None),
            (
                Seq(vec![
                    WithDesc(Box::new(Input("[")), SpanDesc::ParenStart),
                    WithDesc(
                        Box::new(Input("m")),
                        SpanDesc::NameDef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                                SpanDesc::NameRef(NameScopeDesc::Param, Some(NameKindDesc::Value)),
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
                            SpanDesc::NameRef(NameScopeDesc::Instance, Some(NameKindDesc::Value)),
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
                        SpanDesc::NameRef(NameScopeDesc::Instance, Some(NameKindDesc::Function)),
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
                Some(fn_output),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: Vec::new(),
                                }),
                                StrPosition::span_from_range(20..23),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(24..25),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![MappingParam {
                                        mappings: Vec::new(),
                                        notation: WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("a".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::span_from_range(23..24),
                                        ),
                                        data: Vec::new(),
                                    }],
                                }),
                                StrPosition::span_from_range(20..25),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(26..27),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![MappingParam {
                                        mappings: Vec::new(),
                                        notation: WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("a".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: Some(NameKindDesc::Value),
                                            },
                                            StrPosition::span_from_range(23..24),
                                        ),
                                        data: vec![
                                            WithSpan::new(
                                                Token(Ident(":".into(), Unquoted)),
                                                StrPosition::span_from_range(25..26),
                                            ),
                                            WithSpan::new(
                                                Token(Ident("A".into(), Unquoted)),
                                                StrPosition::span_from_range(27..28),
                                            ),
                                        ],
                                    }],
                                }),
                                StrPosition::span_from_range(20..29),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(30..31),
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
                    Input(" := λ _. x"),
                ]),
                Some(ParameterEvent::ParamGroup(Parameterized {
                    parameterizations: Vec::new(),
                    prefixes: Vec::new(),
                    data: Some(ParamGroup {
                        param_notations: vec![WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![MappingParam {
                                        mappings: Vec::new(),
                                        notation: WithSpan::new(
                                            Notation {
                                                expr: None,
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::span_from_range(23..24),
                                        ),
                                        data: Vec::new(),
                                    }],
                                }),
                                StrPosition::span_from_range(20..25),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(26..27),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "a".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(24..25),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(21..26),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(27..28),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::span_from_range(28..29),
                                        ),
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestPrefixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "b".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(33..34),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(30..35),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("y".into(), Unquoted)),
                                            StrPosition::span_from_range(36..37),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..38),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("a".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::span_from_range(23..24),
                                            ),
                                            data: Vec::new(),
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("b".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::span_from_range(25..26),
                                            ),
                                            data: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..27),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(28..29),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("a".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::span_from_range(23..24),
                                            ),
                                            data: Vec::new(),
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("b".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::span_from_range(25..26),
                                            ),
                                            data: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..28),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("a".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::span_from_range(23..24),
                                            ),
                                            data: Vec::new(),
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("b".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: None,
                                                },
                                                StrPosition::span_from_range(26..27),
                                            ),
                                            data: Vec::new(),
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..28),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("a".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(23..24),
                                            ),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(25..26),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("A".into(), Unquoted)),
                                                    StrPosition::span_from_range(27..28),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("b".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(30..31),
                                            ),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(32..33),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("B".into(), Unquoted)),
                                                    StrPosition::span_from_range(34..35),
                                                ),
                                            ],
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..36),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(37..38),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![MappingParam {
                                        mappings: Vec::new(),
                                        notation: WithSpan::new(
                                            Notation {
                                                expr: Some(NotationExpr::Ident("a".into())),
                                                scope: NameScopeDesc::Param,
                                                kind: None,
                                            },
                                            StrPosition::span_from_range(23..24),
                                        ),
                                        data: Vec::new(),
                                    }],
                                }),
                                StrPosition::span_from_range(20..24),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![WithSpan::new(
                                        Mapping(super::Mapping {
                                            kind: &TestPrefixMapping,
                                            params: vec![MappingParam {
                                                mappings: Vec::new(),
                                                notation: WithSpan::new(
                                                    Notation {
                                                        expr: Some(NotationExpr::Ident("a".into())),
                                                        scope: NameScopeDesc::Param,
                                                        kind: None,
                                                    },
                                                    StrPosition::span_from_range(24..25),
                                                ),
                                                data: Vec::new(),
                                            }],
                                        }),
                                        StrPosition::span_from_range(21..25),
                                    )],
                                ),
                                StrPosition::span_from_range(20..26),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("a".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(23..24),
                                            ),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(25..26),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("A".into(), Unquoted)),
                                                    StrPosition::span_from_range(27..28),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: vec![super::Mapping {
                                                kind: &TestPrefixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "b".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::span_from_range(33..34),
                                                    ),
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::span_from_range(35..36),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("B".into(), Unquoted)),
                                                            StrPosition::span_from_range(37..38),
                                                        ),
                                                    ],
                                                }],
                                            }],
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Seq(vec![
                                                        WithSpan::new(
                                                            NotationExpr::Ident("c".into()),
                                                            StrPosition::span_from_range(40..41),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::ReservedChar('_'),
                                                            StrPosition::span_from_range(41..42),
                                                        ),
                                                        WithSpan::new(
                                                            NotationExpr::Param(-1),
                                                            StrPosition::span_from_range(42..43),
                                                        ),
                                                    ])),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Function),
                                                },
                                                StrPosition::span_from_range(40..43),
                                            ),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(44..45),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("C".into(), Unquoted)),
                                                    StrPosition::span_from_range(46..47),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("d".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(49..50),
                                            ),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(51..52),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("D".into(), Unquoted)),
                                                    StrPosition::span_from_range(53..54),
                                                ),
                                            ],
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..55),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(56..57),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Mapping(super::Mapping {
                                    kind: &TestPrefixMapping,
                                    params: vec![
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("a".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(23..24),
                                            ),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(25..26),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("A".into(), Unquoted)),
                                                    StrPosition::span_from_range(27..28),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("b".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(30..31),
                                            ),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(32..33),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("B".into(), Unquoted)),
                                                    StrPosition::span_from_range(34..35),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("↦".into(), Unquoted)),
                                                    StrPosition::span_from_range(36..39),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("c".into(), Unquoted)),
                                                    StrPosition::span_from_range(40..41),
                                                ),
                                                WithSpan::new(
                                                    Token(ReservedChar(
                                                        '_',
                                                        StronglyConnected,
                                                        StronglyConnected,
                                                    )),
                                                    StrPosition::span_from_range(41..42),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("b".into(), Unquoted)),
                                                    StrPosition::span_from_range(42..43),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(44..45),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("C".into(), Unquoted)),
                                                    StrPosition::span_from_range(46..47),
                                                ),
                                            ],
                                        },
                                        MappingParam {
                                            mappings: Vec::new(),
                                            notation: WithSpan::new(
                                                Notation {
                                                    expr: Some(NotationExpr::Ident("d".into())),
                                                    scope: NameScopeDesc::Param,
                                                    kind: Some(NameKindDesc::Value),
                                                },
                                                StrPosition::span_from_range(49..50),
                                            ),
                                            data: vec![
                                                WithSpan::new(
                                                    Token(Ident(":".into(), Unquoted)),
                                                    StrPosition::span_from_range(51..52),
                                                ),
                                                WithSpan::new(
                                                    Token(Ident("D".into(), Unquoted)),
                                                    StrPosition::span_from_range(53..54),
                                                ),
                                            ],
                                        },
                                    ],
                                }),
                                StrPosition::span_from_range(20..55),
                            ),
                            WithSpan::new(
                                Token(Ident("x".into(), Unquoted)),
                                StrPosition::span_from_range(56..57),
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
                        notation: WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("b".into())),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(25..26),
                        ),
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(27..28),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(29..30),
                            ),
                        ],
                    }],
                }),
                StrPosition::span_from_range(22..31),
            ),
            WithSpan::new(
                Token(Ident("b".into(), Unquoted)),
                StrPosition::span_from_range(32..33),
            ),
            WithSpan::new(
                Token(ReservedChar(',', StronglyConnected, Isolated)),
                StrPosition::span_from_range(33..34),
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
                                    notation: WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Ident("d".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(41..42),
                                    ),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(43..44),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("D".into(), Unquoted)),
                                            StrPosition::span_from_range(45..46),
                                        ),
                                    ],
                                },
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Ident("e".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(48..49),
                                    ),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(50..51),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::span_from_range(52..53),
                                        ),
                                    ],
                                },
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Ident("f".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(55..56),
                                    ),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(57..58),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::span_from_range(59..60),
                                        ),
                                    ],
                                },
                            ],
                        }],
                        notation: WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("c".into()),
                                        StrPosition::span_from_range(62..63),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '[',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Param(-3),
                                                    StrPosition::span_from_range(64..65),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(66..67),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(63..68),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(62..68),
                        ),
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(69..70),
                            ),
                            WithSpan::new(
                                Token(Ident("C".into(), Unquoted)),
                                StrPosition::span_from_range(71..72),
                            ),
                        ],
                    }],
                }),
                StrPosition::span_from_range(35..73),
            ),
            WithSpan::new(
                Token(Ident("c".into(), Unquoted)),
                StrPosition::span_from_range(74..75),
            ),
            WithSpan::new(
                Paren(
                    '[',
                    vec![
                        WithSpan::new(
                            Token(Number("0".into())),
                            StrPosition::span_from_range(76..77),
                        ),
                        WithSpan::new(
                            Token(ReservedChar(',', StronglyConnected, StronglyConnected)),
                            StrPosition::span_from_range(77..78),
                        ),
                        WithSpan::new(
                            Token(Number("1".into())),
                            StrPosition::span_from_range(78..79),
                        ),
                    ],
                ),
                StrPosition::span_from_range(75..80),
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
                                expr: Some(NotationExpr::Ident("a".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Token(Ident("f".into(), Unquoted)),
                                StrPosition::span_from_range(20..21),
                            ),
                            WithSpan::new(
                                Paren('[', paren_contents),
                                StrPosition::span_from_range(21..81),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                            StrPosition::span_from_range(21..27),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(28..29),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..30),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "a".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(21..22),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(21..26),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(27..28),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..29),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "a".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::span_from_range(21..22),
                                                    ),
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::span_from_range(23..24),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("A".into(), Unquoted)),
                                                            StrPosition::span_from_range(25..26),
                                                        ),
                                                    ],
                                                }],
                                            }),
                                            StrPosition::span_from_range(21..30),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(31..32),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..33),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "a".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(22..23),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(21..28),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(29..30),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..31),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "a".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: Some(NameKindDesc::Value),
                                                        },
                                                        StrPosition::span_from_range(22..23),
                                                    ),
                                                    data: vec![
                                                        WithSpan::new(
                                                            Token(Ident(":".into(), Unquoted)),
                                                            StrPosition::span_from_range(24..25),
                                                        ),
                                                        WithSpan::new(
                                                            Token(Ident("A".into(), Unquoted)),
                                                            StrPosition::span_from_range(26..27),
                                                        ),
                                                    ],
                                                }],
                                            }),
                                            StrPosition::span_from_range(21..32),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(33..34),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..35),
                            ),
                        ],
                    }),
                })),
            ),
            (Input(";"), None),
        ]);
        let params = vec![MappingParam {
            mappings: Vec::new(),
            notation: WithSpan::new(
                Notation {
                    expr: Some(NotationExpr::Seq(vec![
                        WithSpan::new(
                            NotationExpr::Ident("a".into()),
                            StrPosition::span_from_range(21..22),
                        ),
                        WithSpan::new(
                            NotationExpr::Paren(
                                '(',
                                vec![vec![WithSpan::new(
                                    NotationExpr::Ident("b".into()),
                                    StrPosition::span_from_range(23..24),
                                )]],
                            ),
                            StrPosition::span_from_range(22..25),
                        ),
                    ])),
                    scope: NameScopeDesc::Param,
                    kind: None,
                },
                StrPosition::span_from_range(21..25),
            ),
            data: Vec::new(),
        }];
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params,
                                            }),
                                            StrPosition::span_from_range(21..29),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(30..31),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..32),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Paren(
                                    '(',
                                    vec![
                                        WithSpan::new(
                                            Token(Ident("a".into(), Unquoted)),
                                            StrPosition::span_from_range(21..22),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::span_from_range(22..23),
                                        ),
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "b".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(24..25),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(24..29),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(30..31),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..32),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "a".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(21..22),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(21..26),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(27..28),
                                        ),
                                        WithSpan::new(
                                            Token(ReservedChar(',', StronglyConnected, Isolated)),
                                            StrPosition::span_from_range(28..29),
                                        ),
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "b".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(30..31),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(30..35),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("y".into(), Unquoted)),
                                            StrPosition::span_from_range(36..37),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..38),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                        notation: WithSpan::new(
                                                            Notation {
                                                                expr: Some(NotationExpr::Ident(
                                                                    "a".into(),
                                                                )),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::span_from_range(22..23),
                                                        ),
                                                        data: Vec::new(),
                                                    },
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: WithSpan::new(
                                                            Notation {
                                                                expr: Some(NotationExpr::Ident(
                                                                    "b".into(),
                                                                )),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::span_from_range(24..25),
                                                        ),
                                                        data: Vec::new(),
                                                    },
                                                ],
                                            }),
                                            StrPosition::span_from_range(21..30),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(31..32),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..33),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                        notation: WithSpan::new(
                                                            Notation {
                                                                expr: Some(NotationExpr::Ident(
                                                                    "a".into(),
                                                                )),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::span_from_range(22..23),
                                                        ),
                                                        data: Vec::new(),
                                                    },
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: WithSpan::new(
                                                            Notation {
                                                                expr: Some(NotationExpr::Ident(
                                                                    "b".into(),
                                                                )),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::span_from_range(24..25),
                                                        ),
                                                        data: Vec::new(),
                                                    },
                                                ],
                                            }),
                                            StrPosition::span_from_range(21..31),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(32..33),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..34),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                        notation: WithSpan::new(
                                                            Notation {
                                                                expr: Some(NotationExpr::Ident(
                                                                    "a".into(),
                                                                )),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::span_from_range(22..23),
                                                        ),
                                                        data: Vec::new(),
                                                    },
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: WithSpan::new(
                                                            Notation {
                                                                expr: Some(NotationExpr::Ident(
                                                                    "b".into(),
                                                                )),
                                                                scope: NameScopeDesc::Param,
                                                                kind: None,
                                                            },
                                                            StrPosition::span_from_range(25..26),
                                                        ),
                                                        data: Vec::new(),
                                                    },
                                                ],
                                            }),
                                            StrPosition::span_from_range(21..31),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(32..33),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..34),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                        notation: WithSpan::new(
                                                            Notation {
                                                                expr: Some(NotationExpr::Ident(
                                                                    "a".into(),
                                                                )),
                                                                scope: NameScopeDesc::Param,
                                                                kind: Some(NameKindDesc::Value),
                                                            },
                                                            StrPosition::span_from_range(22..23),
                                                        ),
                                                        data: vec![
                                                            WithSpan::new(
                                                                Token(Ident(":".into(), Unquoted)),
                                                                StrPosition::span_from_range(
                                                                    24..25,
                                                                ),
                                                            ),
                                                            WithSpan::new(
                                                                Token(Ident("A".into(), Unquoted)),
                                                                StrPosition::span_from_range(
                                                                    26..27,
                                                                ),
                                                            ),
                                                        ],
                                                    },
                                                    MappingParam {
                                                        mappings: Vec::new(),
                                                        notation: WithSpan::new(
                                                            Notation {
                                                                expr: Some(NotationExpr::Ident(
                                                                    "b".into(),
                                                                )),
                                                                scope: NameScopeDesc::Param,
                                                                kind: Some(NameKindDesc::Value),
                                                            },
                                                            StrPosition::span_from_range(29..30),
                                                        ),
                                                        data: vec![
                                                            WithSpan::new(
                                                                Token(Ident(":".into(), Unquoted)),
                                                                StrPosition::span_from_range(
                                                                    31..32,
                                                                ),
                                                            ),
                                                            WithSpan::new(
                                                                Token(Ident("B".into(), Unquoted)),
                                                                StrPosition::span_from_range(
                                                                    33..34,
                                                                ),
                                                            ),
                                                        ],
                                                    },
                                                ],
                                            }),
                                            StrPosition::span_from_range(21..39),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(40..41),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..42),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "a".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(21..22),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(21..26),
                                        ),
                                        WithSpan::new(
                                            Mapping(super::Mapping {
                                                kind: &TestInfixMapping,
                                                params: vec![MappingParam {
                                                    mappings: Vec::new(),
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "b".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(27..28),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(27..32),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(33..34),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..35),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
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
                                                            notation: WithSpan::new(
                                                                Notation {
                                                                    expr: Some(
                                                                        NotationExpr::Ident(
                                                                            "a".into(),
                                                                        ),
                                                                    ),
                                                                    scope: NameScopeDesc::Param,
                                                                    kind: None,
                                                                },
                                                                StrPosition::span_from_range(
                                                                    22..23,
                                                                ),
                                                            ),
                                                            data: Vec::new(),
                                                        }],
                                                    }],
                                                    notation: WithSpan::new(
                                                        Notation {
                                                            expr: Some(NotationExpr::Ident(
                                                                "b".into(),
                                                            )),
                                                            scope: NameScopeDesc::Param,
                                                            kind: None,
                                                        },
                                                        StrPosition::span_from_range(28..29),
                                                    ),
                                                    data: Vec::new(),
                                                }],
                                            }),
                                            StrPosition::span_from_range(21..34),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("x".into(), Unquoted)),
                                            StrPosition::span_from_range(35..36),
                                        ),
                                    ],
                                ),
                                StrPosition::span_from_range(20..37),
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
                            notation: WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Ident("a".into())),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(22..23),
                            ),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(24..25),
                                ),
                                WithSpan::new(
                                    Token(Ident("A".into(), Unquoted)),
                                    StrPosition::span_from_range(26..27),
                                ),
                            ],
                        },
                        MappingParam {
                            mappings: vec![super::Mapping {
                                kind: &TestInfixMapping,
                                params: vec![MappingParam {
                                    mappings: Vec::new(),
                                    notation: WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Ident("b".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(29..30),
                                    ),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(31..32),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(33..34),
                                        ),
                                    ],
                                }],
                            }],
                            notation: WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Seq(vec![
                                        WithSpan::new(
                                            NotationExpr::Ident("c".into()),
                                            StrPosition::span_from_range(39..40),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::ReservedChar('_'),
                                            StrPosition::span_from_range(40..41),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::Param(-1),
                                            StrPosition::span_from_range(41..42),
                                        ),
                                    ])),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(39..42),
                            ),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(43..44),
                                ),
                                WithSpan::new(
                                    Token(Ident("C".into(), Unquoted)),
                                    StrPosition::span_from_range(45..46),
                                ),
                            ],
                        },
                        MappingParam {
                            mappings: Vec::new(),
                            notation: WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Ident("d".into())),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(48..49),
                            ),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(50..51),
                                ),
                                WithSpan::new(
                                    Token(Ident("D".into(), Unquoted)),
                                    StrPosition::span_from_range(52..53),
                                ),
                            ],
                        },
                    ],
                }),
                StrPosition::span_from_range(21..58),
            ),
            WithSpan::new(
                Token(Ident("x".into(), Unquoted)),
                StrPosition::span_from_range(59..60),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Paren('(', paren_contents),
                                StrPosition::span_from_range(20..61),
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
                            notation: WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Ident("a".into())),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(22..23),
                            ),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(24..25),
                                ),
                                WithSpan::new(
                                    Token(Ident("A".into(), Unquoted)),
                                    StrPosition::span_from_range(26..27),
                                ),
                            ],
                        },
                        MappingParam {
                            mappings: vec![super::Mapping {
                                kind: &TestPrefixMapping,
                                params: vec![MappingParam {
                                    mappings: Vec::new(),
                                    notation: WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Ident("b".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(32..33),
                                    ),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(34..35),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("B".into(), Unquoted)),
                                            StrPosition::span_from_range(36..37),
                                        ),
                                    ],
                                }],
                            }],
                            notation: WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Seq(vec![
                                        WithSpan::new(
                                            NotationExpr::Ident("c".into()),
                                            StrPosition::span_from_range(39..40),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::ReservedChar('_'),
                                            StrPosition::span_from_range(40..41),
                                        ),
                                        WithSpan::new(
                                            NotationExpr::Param(-1),
                                            StrPosition::span_from_range(41..42),
                                        ),
                                    ])),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Function),
                                },
                                StrPosition::span_from_range(39..42),
                            ),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(43..44),
                                ),
                                WithSpan::new(
                                    Token(Ident("C".into(), Unquoted)),
                                    StrPosition::span_from_range(45..46),
                                ),
                            ],
                        },
                        MappingParam {
                            mappings: Vec::new(),
                            notation: WithSpan::new(
                                Notation {
                                    expr: Some(NotationExpr::Ident("d".into())),
                                    scope: NameScopeDesc::Param,
                                    kind: Some(NameKindDesc::Value),
                                },
                                StrPosition::span_from_range(48..49),
                            ),
                            data: vec![
                                WithSpan::new(
                                    Token(Ident(":".into(), Unquoted)),
                                    StrPosition::span_from_range(50..51),
                                ),
                                WithSpan::new(
                                    Token(Ident("D".into(), Unquoted)),
                                    StrPosition::span_from_range(52..53),
                                ),
                            ],
                        },
                    ],
                }),
                StrPosition::span_from_range(21..58),
            ),
            WithSpan::new(
                Token(Ident("x".into(), Unquoted)),
                StrPosition::span_from_range(59..60),
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
                                expr: Some(NotationExpr::Ident("f".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Paren('(', paren_contents),
                                StrPosition::span_from_range(20..61),
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
                        notation: WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Ident("b".into())),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Value),
                            },
                            StrPosition::span_from_range(23..24),
                        ),
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(25..26),
                            ),
                            WithSpan::new(
                                Token(Ident("B".into(), Unquoted)),
                                StrPosition::span_from_range(27..28),
                            ),
                        ],
                    }],
                }),
                StrPosition::span_from_range(22..33),
            ),
            WithSpan::new(
                Token(Ident("b".into(), Unquoted)),
                StrPosition::span_from_range(34..35),
            ),
            WithSpan::new(
                Token(ReservedChar(',', StronglyConnected, Isolated)),
                StrPosition::span_from_range(35..36),
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
                                    notation: WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Ident("d".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(39..40),
                                    ),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(41..42),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("D".into(), Unquoted)),
                                            StrPosition::span_from_range(43..44),
                                        ),
                                    ],
                                },
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Ident("e".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(46..47),
                                    ),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(48..49),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::span_from_range(50..51),
                                        ),
                                    ],
                                },
                                MappingParam {
                                    mappings: Vec::new(),
                                    notation: WithSpan::new(
                                        Notation {
                                            expr: Some(NotationExpr::Ident("f".into())),
                                            scope: NameScopeDesc::Param,
                                            kind: Some(NameKindDesc::Value),
                                        },
                                        StrPosition::span_from_range(53..54),
                                    ),
                                    data: vec![
                                        WithSpan::new(
                                            Token(Ident(":".into(), Unquoted)),
                                            StrPosition::span_from_range(55..56),
                                        ),
                                        WithSpan::new(
                                            Token(Ident("E".into(), Unquoted)),
                                            StrPosition::span_from_range(57..58),
                                        ),
                                    ],
                                },
                            ],
                        }],
                        notation: WithSpan::new(
                            Notation {
                                expr: Some(NotationExpr::Seq(vec![
                                    WithSpan::new(
                                        NotationExpr::Ident("c".into()),
                                        StrPosition::span_from_range(64..65),
                                    ),
                                    WithSpan::new(
                                        NotationExpr::Paren(
                                            '[',
                                            vec![vec![
                                                WithSpan::new(
                                                    NotationExpr::Param(-3),
                                                    StrPosition::span_from_range(66..67),
                                                ),
                                                WithSpan::new(
                                                    NotationExpr::Param(-1),
                                                    StrPosition::span_from_range(68..69),
                                                ),
                                            ]],
                                        ),
                                        StrPosition::span_from_range(65..70),
                                    ),
                                ])),
                                scope: NameScopeDesc::Param,
                                kind: Some(NameKindDesc::Function),
                            },
                            StrPosition::span_from_range(64..70),
                        ),
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":".into(), Unquoted)),
                                StrPosition::span_from_range(71..72),
                            ),
                            WithSpan::new(
                                Token(Ident("C".into(), Unquoted)),
                                StrPosition::span_from_range(73..74),
                            ),
                        ],
                    }],
                }),
                StrPosition::span_from_range(37..79),
            ),
            WithSpan::new(
                Token(Ident("c".into(), Unquoted)),
                StrPosition::span_from_range(80..81),
            ),
            WithSpan::new(
                Paren(
                    '[',
                    vec![
                        WithSpan::new(
                            Token(Number("0".into())),
                            StrPosition::span_from_range(82..83),
                        ),
                        WithSpan::new(
                            Token(ReservedChar(',', StronglyConnected, StronglyConnected)),
                            StrPosition::span_from_range(83..84),
                        ),
                        WithSpan::new(
                            Token(Number("1".into())),
                            StrPosition::span_from_range(84..85),
                        ),
                    ],
                ),
                StrPosition::span_from_range(81..86),
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
                                expr: Some(NotationExpr::Ident("a".into())),
                                scope: NameScopeDesc::Global,
                                kind: None,
                            },
                            StrPosition::span_from_range(15..16),
                        )],
                        data: vec![
                            WithSpan::new(
                                Token(Ident(":=".into(), Unquoted)),
                                StrPosition::span_from_range(17..19),
                            ),
                            WithSpan::new(
                                Token(Ident("f".into(), Unquoted)),
                                StrPosition::span_from_range(20..21),
                            ),
                            WithSpan::new(
                                Paren('[', paren_contents),
                                StrPosition::span_from_range(21..87),
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
