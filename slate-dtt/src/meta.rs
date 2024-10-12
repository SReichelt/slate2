// TODO: Generate the definitions in this file from meta.slate2.

use std::vec;

use slate_lang_def::parser::layer3_parameter_identifier::ParamIdx;

use crate::expr::*;

pub struct MetaGlobals {
    // `Type %Type`
    pub type_ty_idx: ParamIdx,

    // `[A : Type] A.Inst %Type`
    pub inst_ty_idx: ParamIdx,

    // `⊥ %Type`
    pub bot_ty_idx: ParamIdx,

    // `⊤ %Type`
    pub top_ty_idx: ParamIdx,

    // `[A %Type; [a : A] B_a %Type] ∏ a. B_a %Type`
    pub pi_ty_idx: ParamIdx,

    // `[A %Type; [a : A] B_a %Type; f : ∏ a. B_a; a : A] f(a) : B_a`
    pub pi_app_term_idx: ParamIdx,

    // `[A,B %Type] A → B %Type`
    pub fn_ty_idx: ParamIdx,

    // `[A %Type; [a : A] B_a %Type] ∑ a. B_a %Type`
    pub sigma_ty_idx: ParamIdx,

    // `[A,B %Type] A × B %Type`
    pub pair_ty_idx: ParamIdx,

    // `[A,B %Type] A ⊕ B %Type`
    pub sum_ty_idx: ParamIdx,
}

// Quoted types and terms are both just terms, but in our code we want to see which is which.
pub type QuotedTypeExpr = TermExpr;
pub type QuotedTermExpr = TermExpr;

#[derive(Clone)]
pub enum QuotedType {
    Bot,
    Top,
    Pi(Box<MappedTypeArgs>),
    Sigma(Box<MappedTypeArgs>),
    Sum(Box<ComposedTypeArgs>),
    // TODO: `Ind`
    Type,
    Verbatim(QuotedTypeExpr),
    Let(Box<QuotedLetType>),
}

impl QuotedType {
    pub fn var(idx: ParamIdx) -> Self {
        // A local variable is expected to refer to one that we created while quoting, whereas a
        // global one requires explicit quotation.
        if idx < 0 {
            QuotedType::Verbatim(TermExpr::var(idx))
        } else {
            QuotedType::Verbatim(TermExpr::QuotedType(Box::new(TypeExpr::var(idx))))
        }
    }

    pub fn pi(
        param_ident: Ident,
        source_ty: QuotedType,
        // Note: `target_ty` lives in a context with one additional param.
        target_ty: QuotedType,
    ) -> Self {
        QuotedType::Pi(Box::new(MappedTypeArgs {
            param_ident,
            source_ty,
            target_ty,
        }))
    }

    pub fn sigma(
        param_ident: Ident,
        source_ty: QuotedType,
        // Note: `target_ty` lives in a context with one additional param.
        target_ty: QuotedType,
    ) -> Self {
        QuotedType::Sigma(Box::new(MappedTypeArgs {
            param_ident,
            source_ty,
            target_ty,
        }))
    }

    pub fn sum(left_ty: QuotedType, right_ty: QuotedType) -> Self {
        QuotedType::Sum(Box::new(ComposedTypeArgs { left_ty, right_ty }))
    }

    pub fn into_quoted_type_expr(self, meta_globals: &MetaGlobals) -> QuotedTypeExpr {
        match self {
            QuotedType::Bot => meta_globals.ty_expr_bot(),
            QuotedType::Top => meta_globals.ty_expr_top(),
            QuotedType::Pi(args) => meta_globals.ty_expr_pi(*args),
            QuotedType::Sigma(args) => meta_globals.ty_expr_sigma(*args),
            QuotedType::Sum(args) => meta_globals.ty_expr_sum(*args),
            QuotedType::Type => meta_globals.ty_expr_type(),
            QuotedType::Verbatim(ty_expr) => ty_expr,
            QuotedType::Let(let_expr) => let_expr.into_quoted_type_expr(meta_globals),
        }
    }

    pub fn into_inst_ty(self, meta_globals: &MetaGlobals) -> TypeExpr {
        match self {
            QuotedType::Bot => meta_globals.inst_ty_bot(),
            QuotedType::Top => meta_globals.inst_ty_top(),
            QuotedType::Pi(args) => meta_globals.inst_ty_pi(*args),
            QuotedType::Sigma(args) => meta_globals.inst_ty_sigma(*args),
            QuotedType::Sum(args) => meta_globals.inst_ty_sum(*args),
            QuotedType::Type => meta_globals.type_ty(),
            QuotedType::Verbatim(ty_expr) => meta_globals.inst_ty(ty_expr),
            QuotedType::Let(let_expr) => let_expr.into_inst_ty(meta_globals),
        }
    }
}

#[derive(Clone)]
pub struct ComposedTypeArgs {
    pub left_ty: QuotedType,
    pub right_ty: QuotedType,
}

impl ComposedTypeArgs {
    fn into_quoted_ctor_args(self, meta_globals: &MetaGlobals) -> Vec<Arg> {
        vec![
            Arg::term(self.left_ty.into_quoted_type_expr(meta_globals)),
            Arg::term(self.right_ty.into_quoted_type_expr(meta_globals)),
        ]
    }

    fn into_inst_ty_args(self, meta_globals: &MetaGlobals) -> Vec<Arg> {
        vec![
            Arg::ty(self.left_ty.into_inst_ty(meta_globals)),
            Arg::ty(self.right_ty.into_inst_ty(meta_globals)),
        ]
    }
}

#[derive(Clone)]
pub struct MappedTypeArgs {
    pub param_ident: Ident,
    pub source_ty: QuotedType,
    // Note: `target_ty` lives in a context with one additional param.
    pub target_ty: QuotedType,
}

impl MappedTypeArgs {
    fn into_quoted_ctor_args(self, meta_globals: &MetaGlobals) -> Vec<Arg> {
        vec![
            Arg::term(self.source_ty.clone().into_quoted_type_expr(meta_globals)),
            Arg {
                value: Some(Parameterized {
                    params: vec![Param {
                        ident: self.param_ident,
                        content: Parameterized::new(ParamContent::term(
                            self.source_ty.into_inst_ty(meta_globals),
                        )),
                    }],
                    inner: ArgValue::Term(self.target_ty.into_quoted_type_expr(meta_globals)),
                }),
            },
        ]
    }

    fn into_inst_ty_args(self, meta_globals: &MetaGlobals) -> Vec<Arg> {
        let source_ty = self.source_ty.into_inst_ty(meta_globals);
        vec![
            Arg::ty(source_ty.clone()),
            Arg {
                value: Some(Parameterized {
                    params: vec![Param {
                        ident: self.param_ident,
                        content: Parameterized::new(ParamContent::term(source_ty)),
                    }],
                    inner: ArgValue::Type(self.target_ty.into_inst_ty(meta_globals)),
                }),
            },
        ]
    }
}

#[derive(Clone)]
pub struct QuotedLetType {
    pub param_ident: Ident,
    pub param_ty: QuotedType,
    pub def_expr: QuotedTermExpr,
    pub inner: QuotedType,
}

impl QuotedLetType {
    fn into_quoted_type_expr(self, meta_globals: &MetaGlobals) -> QuotedTypeExpr {
        TermExpr::Base(BaseExpr::Let(Box::new(Parameterized {
            params: vec![meta_globals.let_param(self.param_ident, self.param_ty, self.def_expr)],
            inner: self.inner.into_quoted_type_expr(meta_globals),
        })))
    }

    fn into_inst_ty(self, meta_globals: &MetaGlobals) -> TypeExpr {
        TypeExpr::Base(BaseExpr::Let(Box::new(Parameterized {
            params: vec![meta_globals.let_param(self.param_ident, self.param_ty, self.def_expr)],
            inner: self.inner.into_inst_ty(meta_globals),
        })))
    }
}

impl MetaGlobals {
    pub fn type_ty(&self) -> TypeExpr {
        TypeExpr::var(self.type_ty_idx)
    }

    pub fn ty_expr_bot(&self) -> QuotedTypeExpr {
        TermExpr::ctor(0, Vec::new())
    }

    pub fn ty_expr_top(&self) -> QuotedTypeExpr {
        TermExpr::ctor(1, Vec::new())
    }

    pub fn ty_expr_pi(&self, args: MappedTypeArgs) -> QuotedTypeExpr {
        TermExpr::ctor(2, args.into_quoted_ctor_args(self))
    }

    pub fn ty_expr_sigma(&self, args: MappedTypeArgs) -> QuotedTypeExpr {
        TermExpr::ctor(3, args.into_quoted_ctor_args(self))
    }

    pub fn ty_expr_sum(&self, args: ComposedTypeArgs) -> QuotedTypeExpr {
        TermExpr::ctor(4, args.into_quoted_ctor_args(self))
    }

    pub fn ty_expr_type(&self) -> QuotedTypeExpr {
        TermExpr::ctor(6, Vec::new())
    }

    pub fn inst_ty(&self, ty_expr: QuotedTypeExpr) -> TypeExpr {
        // Note that if `ty_expr` is `TermExpr::QuotedType(ty)`, this is _not_ the same as `ty`.
        TypeExpr::Base(BaseExpr::Var(VarExpr {
            idx: self.inst_ty_idx,
            args: vec![Arg::term(ty_expr)],
        }))
    }

    pub fn inst_ty_bot(&self) -> TypeExpr {
        TypeExpr::var(self.bot_ty_idx)
    }

    pub fn inst_ty_top(&self) -> TypeExpr {
        TypeExpr::var(self.top_ty_idx)
    }

    pub fn inst_ctor_top(&self) -> TermExpr {
        TermExpr::ctor(0, Vec::new())
    }

    pub fn inst_ty_pi(&self, args: MappedTypeArgs) -> TypeExpr {
        TypeExpr::fun(self.pi_ty_idx, args.into_inst_ty_args(self))
    }

    pub fn inst_ctor_pi(
        &self,
        param_ident: Ident,
        source_ty: QuotedType,
        target_expr: QuotedTermExpr,
    ) -> TermExpr {
        TermExpr::ctor(
            0,
            vec![Arg {
                value: Some(Parameterized {
                    params: vec![Param::term(param_ident, source_ty.into_inst_ty(self))],
                    inner: ArgValue::Term(target_expr),
                }),
            }],
        )
    }

    pub fn inst_ty_sigma(&self, args: MappedTypeArgs) -> TypeExpr {
        TypeExpr::fun(self.sigma_ty_idx, args.into_inst_ty_args(self))
    }

    pub fn inst_ctor_sigma(
        &self,
        left_expr: QuotedTermExpr,
        right_expr: QuotedTermExpr,
    ) -> TermExpr {
        TermExpr::ctor(0, vec![Arg::term(left_expr), Arg::term(right_expr)])
    }

    pub fn inst_ty_sum(&self, args: ComposedTypeArgs) -> TypeExpr {
        TypeExpr::fun(self.sum_ty_idx, args.into_inst_ty_args(self))
    }

    pub fn inst_ctor_sum_left(&self, left_expr: QuotedTermExpr) -> TermExpr {
        TermExpr::ctor(0, vec![Arg::term(left_expr)])
    }

    pub fn inst_ctor_sum_right(&self, right_expr: QuotedTermExpr) -> TermExpr {
        TermExpr::ctor(1, vec![Arg::term(right_expr)])
    }

    fn let_param(&self, ident: Ident, ty: QuotedType, def_expr: QuotedTermExpr) -> Param {
        Param {
            ident,
            content: Parameterized::new(ParamContent::Term {
                ty: ty.into_inst_ty(self),
                def: Some(def_expr),
            }),
        }
    }

    fn pi_term(
        &self,
        param_ident: Ident,
        quoted_param: QuotedParamContent,
        target_expr: QuotedTermExpr,
    ) -> QuotedTermExpr {
        if let Some(def_expr) = quoted_param.def_expr {
            TermExpr::Base(BaseExpr::Let(Box::new(Parameterized {
                params: vec![self.let_param(param_ident, quoted_param.ty, def_expr)],
                inner: target_expr,
            })))
        } else {
            self.inst_ctor_pi(param_ident, quoted_param.ty, target_expr)
        }
    }

    fn quote_type(ty: TypeExpr) -> QuotedTypeExpr {
        // Note that this should cause references to earlier parameters as well as parameterizations
        // to be treated correctly as antiquotations, whereas we want to quote everything else
        // verbatim.
        match ty {
            TypeExpr::Base(BaseExpr::Var(var_expr))
                if !var_expr.is_global() && var_expr.args.is_empty() =>
            {
                // Optimize the common case where the type is a reference to a local variable, which
                // would lead to a single quoted antiquotation.
                TermExpr::Base(BaseExpr::Var(var_expr))
            }
            _ => TermExpr::QuotedType(Box::new(ty)),
        }
    }

    fn quote_term(term: TermExpr) -> QuotedTermExpr {
        // Note that this should cause references to earlier parameters as well as parameterizations
        // to be treated correctly as antiquotations, whereas we want to quote everything else
        // verbatim.
        match term {
            TermExpr::Base(BaseExpr::Var(var_expr))
                if !var_expr.is_global() && var_expr.args.is_empty() =>
            {
                // Optimize the common case where the term is a reference to a local variable, which
                // would lead to a single quoted antiquotation.
                TermExpr::Base(BaseExpr::Var(var_expr))
            }
            _ => TermExpr::QuotedTerm(Box::new(term)),
        }
    }

    fn quote_param_type(&self, content: Parameterized<ParamContent>) -> QuotedParamContent {
        let mut quoted = self.quote_param_content(content.inner);
        for param in content.params.into_iter().rev() {
            let quoted_param = self.quote_param_type(param.content);
            if let Some(quoted_def_expr) = quoted.def_expr {
                quoted.def_expr =
                    Some(self.pi_term(param.ident.clone(), quoted_param.clone(), quoted_def_expr));
            }
            if let Some(def_expr) = quoted_param.def_expr {
                quoted.ty = QuotedType::Let(Box::new(QuotedLetType {
                    param_ident: param.ident,
                    param_ty: quoted_param.ty,
                    def_expr,
                    inner: quoted.ty,
                }))
            } else {
                quoted.ty = QuotedType::pi(param.ident, quoted_param.ty, quoted.ty);
            }
        }
        quoted
    }

    fn quote_param_content(&self, content: ParamContent) -> QuotedParamContent {
        match content {
            ParamContent::Type { def } => QuotedParamContent {
                ty: QuotedType::Type,
                def_expr: def.map(Self::quote_type),
            },
            ParamContent::Term { ty, def } => QuotedParamContent {
                ty: QuotedType::Verbatim(Self::quote_type(ty)),
                def_expr: def.map(Self::quote_term),
            },
        }
    }

    pub fn quote_data_type(&self, data_type: DataType) -> QuotedType {
        let mut param_iter = data_type.ctors.into_iter().rev();
        if let Some(ctor) = param_iter.next() {
            let mut quoted = self.quote_ctor(ctor);
            while let Some(ctor) = param_iter.next() {
                quoted = QuotedType::sum(self.quote_ctor(ctor), quoted);
            }
            quoted
        } else {
            QuotedType::Bot
        }
    }

    fn quote_ctor(&self, ctor: Ctor) -> QuotedType {
        let mut quoted = None;
        for param in ctor.ctor.params.into_iter().rev() {
            let quoted_param = self.quote_param_type(param.content);
            if let Some(def_expr) = quoted_param.def_expr {
                if let Some(inner) = quoted {
                    quoted = Some(QuotedType::Let(Box::new(QuotedLetType {
                        param_ident: param.ident,
                        param_ty: quoted_param.ty,
                        def_expr,
                        inner,
                    })));
                }
            } else {
                let new_quoted = if let Some(quoted) = quoted {
                    QuotedType::sigma(param.ident, quoted_param.ty, quoted)
                } else {
                    quoted_param.ty
                };
                quoted = Some(new_quoted);
            }
        }
        quoted.unwrap_or(QuotedType::Top)
    }

    fn quote_arg_value(&self, arg_value: Parameterized<ArgValue>) -> QuotedTermExpr {
        let mut quoted = match arg_value.inner {
            ArgValue::Type(ty) => Self::quote_type(ty),
            ArgValue::Term(term) => Self::quote_term(term),
        };
        for param in arg_value.params.into_iter().rev() {
            let quoted_param = self.quote_param_type(param.content);
            quoted = self.pi_term(param.ident, quoted_param, quoted);
        }
        quoted
    }

    pub fn quote_ctor_expr(&self, mut ctor_expr: VarExpr, ctors_len: usize) -> QuotedTermExpr {
        let mut quoted = self.quote_ctor_args(ctor_expr.args);
        if ctor_expr.idx + 1 < ctors_len as ParamIdx {
            // For every ctor except the last, the innermost term is wrapped in the "left" sum ctor.
            quoted = self.inst_ctor_sum_left(quoted);
        }
        while ctor_expr.idx > 0 {
            // For every ctor we skip, we have to add a "right" sum ctor.
            quoted = self.inst_ctor_sum_right(quoted);
            ctor_expr.idx -= 1;
        }
        quoted
    }

    fn quote_ctor_args(&self, args: Vec<Arg>) -> QuotedTermExpr {
        let mut arg_iter = args.into_iter().rev().filter_map(|arg| arg.value);
        if let Some(arg_value) = arg_iter.next() {
            let mut quoted = self.quote_arg_value(arg_value);
            while let Some(arg_value) = arg_iter.next() {
                quoted = self.inst_ctor_sigma(self.quote_arg_value(arg_value), quoted);
            }
            quoted
        } else {
            self.inst_ctor_top()
        }
    }
}

#[derive(Clone)]
struct QuotedParamContent {
    pub ty: QuotedType,
    pub def_expr: Option<QuotedTermExpr>,
}

pub mod testing {
    use super::MetaGlobals;

    pub static TEST_META_GLOBALS: MetaGlobals = MetaGlobals {
        type_ty_idx: 0,
        inst_ty_idx: 1,
        bot_ty_idx: 2,
        top_ty_idx: 3,
        pi_ty_idx: 4,
        pi_app_term_idx: 5,
        fn_ty_idx: 6,
        sigma_ty_idx: 7,
        pair_ty_idx: 8,
        sum_ty_idx: 9,
    };
}

#[cfg(test)]
mod tests {
    use super::{testing::*, *};

    fn assert_quote_data_type(data_type: DataType, expected_ty: QuotedType) {
        let input_dbg = format!("{data_type:?}");
        let result_ty_expr = TEST_META_GLOBALS
            .quote_data_type(data_type)
            .into_quoted_type_expr(&TEST_META_GLOBALS);
        println!("{input_dbg} -> {result_ty_expr:?}");
        assert_eq!(
            result_ty_expr,
            expected_ty.into_quoted_type_expr(&TEST_META_GLOBALS),
            "quoting {input_dbg} did not yield expected result"
        )
    }

    #[test]
    fn quote_data_types() {
        // `{}`
        assert_quote_data_type(DataType { ctors: Vec::new() }, QuotedType::Bot);

        // `{ c }`
        assert_quote_data_type(
            DataType {
                ctors: vec![Ctor::new(Ident::new("c"), Vec::new())],
            },
            QuotedType::Top,
        );

        // `{ c(A) | A %Type }`
        assert_quote_data_type(
            DataType {
                ctors: vec![Ctor::new(Ident::new("c"), vec![Param::ty(Ident::new("A"))])],
            },
            QuotedType::Type,
        );

        // `{ c(A, a) | A %Type; a : A }`
        assert_quote_data_type(
            DataType {
                ctors: vec![Ctor::new(
                    Ident::new("c"),
                    vec![
                        Param::ty(Ident::new("A")),
                        Param::term(Ident::new("a"), TypeExpr::var(-1)),
                    ],
                )],
            },
            QuotedType::sigma(Ident::new("A"), QuotedType::Type, QuotedType::var(-1)),
        );

        // `{ c(A, a, b) | A %Type; a,b : A }`
        assert_quote_data_type(
            DataType {
                ctors: vec![Ctor::new(
                    Ident::new("c"),
                    vec![
                        Param::ty(Ident::new("A")),
                        Param::term(Ident::new("a"), TypeExpr::var(-1)),
                        Param::term(Ident::new("b"), TypeExpr::var(-2)),
                    ],
                )],
            },
            QuotedType::sigma(
                Ident::new("A"),
                QuotedType::Type,
                QuotedType::sigma(Ident::new("a"), QuotedType::var(-1), QuotedType::var(-2)),
            ),
        );

        // `{ c || d(A) | A %Type }`
        assert_quote_data_type(
            DataType {
                ctors: vec![
                    Ctor::new(Ident::new("c"), Vec::new()),
                    Ctor::new(Ident::new("d"), vec![Param::ty(Ident::new("A"))]),
                ],
            },
            QuotedType::sum(QuotedType::Top, QuotedType::Type),
        );

        // `{ c || d(A) | A %Type || e(B, D) | B %Type; C :≡ B; c : C }`
        assert_quote_data_type(
            DataType {
                ctors: vec![
                    Ctor::new(Ident::new("c"), Vec::new()),
                    Ctor::new(Ident::new("d"), vec![Param::ty(Ident::new("A"))]),
                    Ctor::new(
                        Ident::new("e"),
                        vec![
                            Param::ty(Ident::new("B")),
                            Param {
                                ident: Ident::new("C"),
                                content: Parameterized::new(ParamContent::Type {
                                    def: Some(TypeExpr::var(-1)),
                                }),
                            },
                            Param::term(Ident::new("c"), TypeExpr::var(-1)),
                        ],
                    ),
                ],
            },
            QuotedType::sum(
                QuotedType::Top,
                QuotedType::sum(
                    QuotedType::Type,
                    QuotedType::sigma(
                        Ident::new("B"),
                        QuotedType::Type,
                        QuotedType::Let(Box::new(QuotedLetType {
                            param_ident: Ident::new("C"),
                            param_ty: QuotedType::Type,
                            def_expr: TermExpr::var(-1),
                            inner: QuotedType::var(-1),
                        })),
                    ),
                ),
            ),
        );

        // `{ c(A ↦ B(A)) | [A %Type] B(A) %Type }`
        assert_quote_data_type(
            DataType {
                ctors: vec![Ctor::new(
                    Ident::new("c"),
                    vec![Param {
                        ident: Ident::new("B"),
                        content: Parameterized {
                            params: vec![Param::ty(Ident::new("A"))],
                            inner: ParamContent::ty(),
                        },
                    }],
                )],
            },
            QuotedType::pi(Ident::new("A"), QuotedType::Type, QuotedType::Type),
        );

        // `{ c(A, B, a ↦ b(a)) | A,B %Type; [a : A] b(a) : B }`
        assert_quote_data_type(
            DataType {
                ctors: vec![Ctor::new(
                    Ident::new("c"),
                    vec![
                        Param::ty(Ident::new("A")),
                        Param::ty(Ident::new("B")),
                        Param {
                            ident: Ident::new("b"),
                            content: Parameterized {
                                params: vec![Param::term(Ident::new("a"), TypeExpr::var(-2))],
                                inner: ParamContent::term(TypeExpr::var(-2)),
                            },
                        },
                    ],
                )],
            },
            QuotedType::sigma(
                Ident::new("A"),
                QuotedType::Type,
                QuotedType::sigma(
                    Ident::new("B"),
                    QuotedType::Type,
                    QuotedType::pi(Ident::new("a"), QuotedType::var(-2), QuotedType::var(-2)),
                ),
            ),
        );

        // `{ c((A, b) ↦ C(A, b)) | [A %Type; B :≡ A; b : B] C(A, b) %Type }`
        assert_quote_data_type(
            DataType {
                ctors: vec![Ctor::new(
                    Ident::new("c"),
                    vec![Param {
                        ident: Ident::new("C"),
                        content: Parameterized {
                            params: vec![
                                Param::ty(Ident::new("A")),
                                Param {
                                    ident: Ident::new("B"),
                                    content: Parameterized::new(ParamContent::Type {
                                        def: Some(TypeExpr::var(-1)),
                                    }),
                                },
                                Param::term(Ident::new("b"), TypeExpr::var(-1)),
                            ],
                            inner: ParamContent::ty(),
                        },
                    }],
                )],
            },
            QuotedType::pi(
                Ident::new("A"),
                QuotedType::Type,
                QuotedType::Let(Box::new(QuotedLetType {
                    param_ident: Ident::new("B"),
                    param_ty: QuotedType::Type,
                    def_expr: TermExpr::var(-1),
                    inner: QuotedType::pi(Ident::new("b"), QuotedType::var(-1), QuotedType::Type),
                })),
            ),
        );

        // `{ c((A, b) ↦ C(A, b), (A, b) ↦ D(A, b), (A, b) ↦ d(A, b)) |
        //      [A %Type; B :≡ A; b : B] { C(A, b) %Type; D(A, b) :≡ C(A, b); d(A, b) : D(A, b); } }`
        assert_quote_data_type(
            DataType {
                ctors: vec![Ctor::new(
                    Ident::new("c"),
                    vec![
                        Param {
                            ident: Ident::new("C"),
                            content: Parameterized {
                                params: vec![
                                    Param::ty(Ident::new("A")),
                                    Param {
                                        ident: Ident::new("B"),
                                        content: Parameterized::new(ParamContent::Type {
                                            def: Some(TypeExpr::var(-1)),
                                        }),
                                    },
                                    Param::term(Ident::new("b"), TypeExpr::var(-1)),
                                ],
                                inner: ParamContent::ty(),
                            },
                        },
                        Param {
                            ident: Ident::new("D"),
                            content: Parameterized {
                                params: vec![
                                    Param::ty(Ident::new("A")),
                                    Param {
                                        ident: Ident::new("B"),
                                        content: Parameterized::new(ParamContent::Type {
                                            def: Some(TypeExpr::var(-1)),
                                        }),
                                    },
                                    Param::term(Ident::new("b"), TypeExpr::var(-1)),
                                ],
                                inner: ParamContent::Type {
                                    def: Some(TypeExpr::Base(BaseExpr::Var(VarExpr {
                                        idx: -4,
                                        args: vec![
                                            Arg::ty(TypeExpr::var(-3)),
                                            Arg::def(),
                                            Arg::term(TermExpr::var(-1)),
                                        ],
                                    }))),
                                },
                            },
                        },
                        Param {
                            ident: Ident::new("d"),
                            content: Parameterized {
                                params: vec![
                                    Param::ty(Ident::new("A")),
                                    Param {
                                        ident: Ident::new("B"),
                                        content: Parameterized::new(ParamContent::Type {
                                            def: Some(TypeExpr::var(-1)),
                                        }),
                                    },
                                    Param::term(Ident::new("b"), TypeExpr::var(-1)),
                                ],
                                inner: ParamContent::term(TypeExpr::Base(BaseExpr::Var(VarExpr {
                                    idx: -4,
                                    args: vec![
                                        Arg::ty(TypeExpr::var(-3)),
                                        Arg::def(),
                                        Arg::term(TermExpr::var(-1)),
                                    ],
                                }))),
                            },
                        },
                    ],
                )],
            },
            QuotedType::sigma(
                Ident::new("C"),
                QuotedType::pi(
                    Ident::new("A"),
                    QuotedType::Type,
                    QuotedType::Let(Box::new(QuotedLetType {
                        param_ident: Ident::new("B"),
                        param_ty: QuotedType::Type,
                        def_expr: TermExpr::var(-1),
                        inner: QuotedType::pi(
                            Ident::new("b"),
                            QuotedType::var(-1),
                            QuotedType::Type,
                        ),
                    })),
                ),
                QuotedType::Let(Box::new(QuotedLetType {
                    param_ident: Ident::new("D"),
                    param_ty: QuotedType::pi(
                        Ident::new("A"),
                        QuotedType::Type,
                        QuotedType::Let(Box::new(QuotedLetType {
                            param_ident: Ident::new("B"),
                            param_ty: QuotedType::Type,
                            def_expr: TermExpr::var(-1),
                            inner: QuotedType::pi(
                                Ident::new("b"),
                                QuotedType::var(-1),
                                QuotedType::Type,
                            ),
                        })),
                    ),
                    def_expr: TEST_META_GLOBALS.inst_ctor_pi(
                        Ident::new("A"),
                        QuotedType::Type,
                        TermExpr::Base(BaseExpr::Let(Box::new(Parameterized {
                            params: vec![Param {
                                ident: Ident::new("B"),
                                content: Parameterized::new(ParamContent::Term {
                                    ty: TEST_META_GLOBALS.type_ty(),
                                    def: Some(TermExpr::var(-1)),
                                }),
                            }],
                            inner: TEST_META_GLOBALS.inst_ctor_pi(
                                Ident::new("b"),
                                QuotedType::var(-1),
                                TermExpr::QuotedType(Box::new(TypeExpr::Base(BaseExpr::Var(
                                    VarExpr {
                                        idx: -4,
                                        args: vec![
                                            Arg::ty(TypeExpr::var(-3)),
                                            Arg::def(),
                                            Arg::term(TermExpr::var(-1)),
                                        ],
                                    },
                                )))),
                            ),
                        }))),
                    ),
                    inner: QuotedType::pi(
                        Ident::new("A"),
                        QuotedType::Type,
                        QuotedType::Let(Box::new(QuotedLetType {
                            param_ident: Ident::new("B"),
                            param_ty: QuotedType::Type,
                            def_expr: TermExpr::var(-1),
                            inner: QuotedType::pi(
                                Ident::new("b"),
                                QuotedType::var(-1),
                                QuotedType::Verbatim(TermExpr::QuotedType(Box::new(
                                    TypeExpr::Base(BaseExpr::Var(VarExpr {
                                        idx: -4,
                                        args: vec![
                                            Arg::ty(TypeExpr::var(-3)),
                                            Arg::def(),
                                            Arg::term(TermExpr::var(-1)),
                                        ],
                                    })),
                                ))),
                            ),
                        })),
                    ),
                })),
            ),
        );

        // `{ c(a ↦ B(a), a ↦ b(a)) | [a : #42] B(a) %Type; [a : #42] b(a) : B(a) }`
        assert_quote_data_type(
            DataType {
                ctors: vec![Ctor::new(
                    Ident::new("c"),
                    vec![
                        Param {
                            ident: Ident::new("B"),
                            content: Parameterized {
                                params: vec![Param::term(Ident::new("a"), TypeExpr::var(42))],
                                inner: ParamContent::ty(),
                            },
                        },
                        Param {
                            ident: Ident::new("b"),
                            content: Parameterized {
                                params: vec![Param::term(Ident::new("a"), TypeExpr::var(42))],
                                inner: ParamContent::term(TypeExpr::Base(BaseExpr::Var(VarExpr {
                                    idx: -2,
                                    args: vec![Arg::term(TermExpr::var(-1))],
                                }))),
                            },
                        },
                    ],
                )],
            },
            QuotedType::sigma(
                Ident::new("B"),
                QuotedType::pi(Ident::new("a"), QuotedType::var(42), QuotedType::Type),
                QuotedType::pi(
                    Ident::new("a"),
                    QuotedType::var(42),
                    QuotedType::Verbatim(TermExpr::QuotedType(Box::new(TypeExpr::Base(
                        BaseExpr::Var(VarExpr {
                            idx: -2,
                            args: vec![Arg::term(TermExpr::var(-1))],
                        }),
                    )))),
                ),
            ),
        );
    }

    fn assert_quote_ctor_expr(ctor_expr: VarExpr, ctors_len: usize, expected_expr: QuotedTermExpr) {
        let input_dbg = format!("_.{ctor_expr:?} ({ctors_len} ctor(s))");
        let result_expr = TEST_META_GLOBALS.quote_ctor_expr(ctor_expr, ctors_len);
        println!("{input_dbg} -> {result_expr:?}");
        assert_eq!(
            result_expr, expected_expr,
            "quoting {input_dbg} did not yield expected result"
        )
    }

    #[test]
    fn quote_ctor_exprs() {
        // `c` in `{ c }` (`⊤`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 0,
                args: Vec::new(),
            },
            1,
            TEST_META_GLOBALS.inst_ctor_top(),
        );

        // `c` in `{ c | d }` (`⊤ ⊕ ⊤`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 0,
                args: Vec::new(),
            },
            2,
            TEST_META_GLOBALS.inst_ctor_sum_left(TEST_META_GLOBALS.inst_ctor_top()),
        );

        // `d` in `{ c | d }` (`⊤ ⊕ ⊤`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 1,
                args: Vec::new(),
            },
            2,
            TEST_META_GLOBALS.inst_ctor_sum_right(TEST_META_GLOBALS.inst_ctor_top()),
        );

        // `c` in `{ c | d | e }` (`⊤ ⊕ (⊤ ⊕ ⊤)`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 0,
                args: Vec::new(),
            },
            3,
            TEST_META_GLOBALS.inst_ctor_sum_left(TEST_META_GLOBALS.inst_ctor_top()),
        );

        // `d` in `{ c | d | e }` (`⊤ ⊕ (⊤ ⊕ ⊤)`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 1,
                args: Vec::new(),
            },
            3,
            TEST_META_GLOBALS.inst_ctor_sum_right(
                TEST_META_GLOBALS.inst_ctor_sum_left(TEST_META_GLOBALS.inst_ctor_top()),
            ),
        );

        // `e` in `{ c | d | e }` (`⊤ ⊕ (⊤ ⊕ ⊤)`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 2,
                args: Vec::new(),
            },
            3,
            TEST_META_GLOBALS.inst_ctor_sum_right(
                TEST_META_GLOBALS.inst_ctor_sum_right(TEST_META_GLOBALS.inst_ctor_top()),
            ),
        );

        // `c(#42)` in `{ c(A) | A %Type }` (`Type`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 0,
                args: vec![Arg::ty(TypeExpr::var(42))],
            },
            1,
            TermExpr::QuotedType(Box::new(TypeExpr::var(42))),
        );

        // `c(#42, #23)` in `{ c(A, B) | A,B %Type }` (`Type × Type`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 0,
                args: vec![Arg::ty(TypeExpr::var(42)), Arg::ty(TypeExpr::var(23))],
            },
            1,
            TEST_META_GLOBALS.inst_ctor_sigma(
                TermExpr::QuotedType(Box::new(TypeExpr::var(42))),
                TermExpr::QuotedType(Box::new(TypeExpr::var(23))),
            ),
        );

        // `c(#42, #23, #43)` in `{ c(A, B, C) | A,B,C %Type }` (`Type × (Type × Type)`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 0,
                args: vec![
                    Arg::ty(TypeExpr::var(42)),
                    Arg::ty(TypeExpr::var(23)),
                    Arg::ty(TypeExpr::var(43)),
                ],
            },
            1,
            TEST_META_GLOBALS.inst_ctor_sigma(
                TermExpr::QuotedType(Box::new(TypeExpr::var(42))),
                TEST_META_GLOBALS.inst_ctor_sigma(
                    TermExpr::QuotedType(Box::new(TypeExpr::var(23))),
                    TermExpr::QuotedType(Box::new(TypeExpr::var(43))),
                ),
            ),
        );

        // `c(#42, a ↦ a)` in `{ c(A, a ↦ b_a) | A %Type; [a : A] b_a : A }`
        //                    (`∑ A : Type. A.Inst → A.Inst`)
        assert_quote_ctor_expr(
            VarExpr {
                idx: 0,
                args: vec![
                    Arg::ty(TypeExpr::var(42)),
                    Arg {
                        value: Some(Parameterized {
                            params: vec![Param::term(Ident::new("a"), TypeExpr::var(42))],
                            inner: ArgValue::Term(TermExpr::var(-1)),
                        }),
                    },
                ],
            },
            1,
            TEST_META_GLOBALS.inst_ctor_sigma(
                TermExpr::QuotedType(Box::new(TypeExpr::var(42))),
                TEST_META_GLOBALS.inst_ctor_pi(
                    Ident::new("a"),
                    QuotedType::var(42),
                    TermExpr::var(-1),
                ),
            ),
        );
    }
}