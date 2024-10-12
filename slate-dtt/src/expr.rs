// The expressions defined here reflect what the parser produces based on the information available
// to it. In particular, terms are not necessarily well-typed because the parser cannot perform full
// type computation. Moreover, quoted expressions are parsed in the surrounding context, even though
// most variables from that context are not valid antiquotations.
//
// The code relies on parameters and arguments fitting together, and on constructors fitting the
// expected data types, but not on well-typedness of terms in general. To interpret a given term, it
// is often necessary to know its type.

use std::{
    borrow::Cow,
    fmt::{self, Debug, Formatter},
    mem::replace,
};

use slate_lang_def::parser::layer3_parameter_identifier::ParamIdx;

use crate::context::*;

#[derive(Clone)]
pub struct Ident {
    pub name: Option<&'static str>,
}

impl Ident {
    pub const fn new(name: &'static str) -> Self {
        Ident { name: Some(name) }
    }

    pub const fn none() -> Self {
        Self { name: None }
    }
}

impl Default for Ident {
    fn default() -> Self {
        Self::none()
    }
}

impl PartialEq for Ident {
    fn eq(&self, _other: &Self) -> bool {
        // All idents are considered equal, as we use De Bruijn indices and levels to refer to
        // params.
        true
    }
}

impl Debug for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name {
            f.write_str(name)
        } else {
            f.write_str("_")
        }
    }
}

impl Eq for Ident {}

#[derive(Clone, PartialEq, Eq)]
pub struct Parameterized<T> {
    pub params: Vec<Param>,
    pub inner: T,
}

impl<T> Parameterized<T> {
    pub const fn new(inner: T) -> Self {
        Parameterized {
            params: Vec::new(),
            inner,
        }
    }
}

impl<T: Debug> Debug for Parameterized<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Param::dbg_fmt_params(&self.params, f)?;
        self.inner.fmt(f)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Param {
    pub ident: Ident,
    pub content: Parameterized<ParamContent>,
}

impl Param {
    pub const fn ty(ident: Ident) -> Self {
        Param {
            ident,
            content: Parameterized::new(ParamContent::ty()),
        }
    }

    pub const fn term(ident: Ident, ty: TypeExpr) -> Self {
        Param {
            ident,
            content: Parameterized::new(ParamContent::term(ty)),
        }
    }

    pub const fn is_def(&self) -> bool {
        self.content.inner.is_def()
    }

    fn dbg_fmt_params(params: &[Self], f: &mut Formatter<'_>) -> fmt::Result {
        let mut param_iter = params.iter();
        if let Some(param) = param_iter.next() {
            f.write_str("[")?;
            param.fmt(f)?;
            while let Some(param) = param_iter.next() {
                f.write_str("; ")?;
                param.fmt(f)?;
            }
            f.write_str("] ")?;
        }
        Ok(())
    }

    fn dbg_fmt_arg(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut param_iter = self.content.params.iter().filter(|param| !param.is_def());
        if let Some(param) = param_iter.next() {
            if let Some(param2) = param_iter.next() {
                f.write_str("(")?;
                param.dbg_fmt_arg(f)?;
                f.write_str(", ")?;
                param2.dbg_fmt_arg(f)?;
                while let Some(param) = param_iter.next() {
                    f.write_str(", ")?;
                    param.dbg_fmt_arg(f)?;
                }
                f.write_str(")")?;
            } else {
                param.dbg_fmt_arg(f)?;
            }
            f.write_str(" ↦ ")?;
        }
        self.ident.fmt(f)?;
        Self::dbg_fmt_args(&self.content.params, f)
    }

    fn dbg_fmt_args(params: &[Self], f: &mut Formatter<'_>) -> fmt::Result {
        let mut param_iter = params.iter().filter(|param| !param.is_def());
        if let Some(param) = param_iter.next() {
            f.write_str("(")?;
            param.dbg_fmt_arg(f)?;
            while let Some(param) = param_iter.next() {
                f.write_str(", ")?;
                param.dbg_fmt_arg(f)?;
            }
            f.write_str(")")?;
        }
        Ok(())
    }
}

impl Debug for Param {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Param::dbg_fmt_params(&self.content.params, f)?;
        self.ident.fmt(f)?;
        Param::dbg_fmt_args(&self.content.params, f)?;
        self.content.inner.fmt(f)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum ParamContent {
    Type { def: Option<TypeExpr> },
    Term { ty: TypeExpr, def: Option<TermExpr> },
}

impl ParamContent {
    pub const fn ty() -> Self {
        ParamContent::Type { def: None }
    }

    pub const fn term(ty: TypeExpr) -> Self {
        ParamContent::Term { ty, def: None }
    }

    pub const fn is_def(&self) -> bool {
        match self {
            ParamContent::Type { def } => def.is_some(),
            ParamContent::Term { def, .. } => def.is_some(),
        }
    }
}

impl Debug for ParamContent {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ParamContent::Type { def } => {
                f.write_str(" %Type")?;
                if let Some(def) = def {
                    f.write_str(" :≡ ")?;
                    def.fmt(f)?;
                }
            }
            ParamContent::Term { ty, def } => {
                f.write_str(" : ")?;
                ty.fmt(f)?;
                if let Some(def) = def {
                    f.write_str(" :≡ ")?;
                    def.fmt(f)?;
                }
            }
        }
        Ok(())
    }
}

// An argument corresponding to a given `Param`.
#[derive(Clone, PartialEq, Eq)]
pub struct Arg {
    // The type or term (depending on the param), parameterized equivalently to the param. `None` if
    // the param is a definition.
    // Note that substituting a term arg generally requires inserting a cast (to the param type) at
    // every place where the param was replaced with the arg. E.g. if the param type is
    // `%Any(A,B|e)`, it may be used as a term of type `A`, while the arg could be a term of type
    // `B` via an implicit cast. In this case, the cast to `%Any(A,B|e)` reduces to applying the
    // reverse direction of `e`.
    pub value: Option<Parameterized<ArgValue>>,
}

impl Arg {
    pub const fn def() -> Self {
        Arg { value: None }
    }

    pub const fn term(term: TermExpr) -> Self {
        Arg {
            value: Some(Parameterized::new(ArgValue::Term(term))),
        }
    }

    pub const fn ty(ty: TypeExpr) -> Self {
        Arg {
            value: Some(Parameterized::new(ArgValue::Type(ty))),
        }
    }

    fn dbg_fmt_args(args: &[Self], f: &mut Formatter<'_>) -> fmt::Result {
        let mut arg_iter = args.iter().filter(|arg| arg.value.is_some());
        if let Some(arg) = arg_iter.next() {
            f.write_str("(")?;
            arg.fmt(f)?;
            while let Some(arg) = arg_iter.next() {
                f.write_str(", ")?;
                arg.fmt(f)?;
            }
            f.write_str(")")?;
        }
        Ok(())
    }
}

impl Debug for Arg {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(value) = &self.value {
            let mut param_iter = value.params.iter().filter(|param| !param.is_def());
            if let Some(param) = param_iter.next() {
                f.write_str("(")?;
                param.fmt(f)?;
                while let Some(param) = param_iter.next() {
                    f.write_str(", ")?;
                    param.fmt(f)?;
                }
                f.write_str(") ↦ ")?;
            }
            value.inner.fmt(f)
        } else {
            f.write_str("_")
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum ArgValue {
    Type(TypeExpr),
    Term(TermExpr),
}

impl Debug for ArgValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ArgValue::Type(ty) => ty.fmt(f),
            ArgValue::Term(term) => term.fmt(f),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum BaseExpr<T, Ty> {
    // A placeholder or error expression that should be propagated as far as possible in order to
    // produce more useful diagnostics.
    Placeholder,

    // Variable reference, with exactly one arg per parameterization.
    Var(VarExpr),

    // Let-binding. All params must be definitions.
    Let(Box<Parameterized<T>>),

    // Matching on a term.
    Match(Box<MatchExpr<T, Ty>>),

    // Projection, which is essentially a shorthand for matching on a single constructor.
    Proj(Box<ProjExpr>),
}

impl<T, Ty> Default for BaseExpr<T, Ty> {
    fn default() -> Self {
        BaseExpr::Placeholder
    }
}

impl<T: Debug, Ty: Debug> Debug for BaseExpr<T, Ty> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            BaseExpr::Placeholder => f.write_str("_"),
            BaseExpr::Var(var_expr) => var_expr.fmt(f),
            BaseExpr::Let(let_expr) => let_expr.fmt(f),
            BaseExpr::Match(match_expr) => match_expr.fmt(f),
            BaseExpr::Proj(proj_expr) => proj_expr.fmt(f),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct VarExpr {
    pub idx: ParamIdx,
    pub args: Vec<Arg>,
}

impl VarExpr {
    pub const fn new(idx: ParamIdx) -> Self {
        VarExpr {
            idx,
            args: Vec::new(),
        }
    }

    pub const fn is_global(&self) -> bool {
        self.idx >= 0
    }
}

impl Debug for VarExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.idx)?;
        Arg::dbg_fmt_args(&self.args, f)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct TypedExpr<T, Ty> {
    pub ty: Ty,
    pub value: T,
}

impl<T: Debug, Ty: Debug> Debug for TypedExpr<T, Ty> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if size_of::<Ty>() > 0 {
            f.write_str("(")?;
            self.value.fmt(f)?;
            f.write_str(" : ")?;
            self.ty.fmt(f)?;
            f.write_str(")")
        } else {
            self.value.fmt(f)
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct MatchExpr<T, Ty> {
    // The term to match on, whose type must reduce to a data type definition.
    pub match_term: TypedExpr<TermExpr, TypeExpr>,

    // Exactly one arm for each constructor of the data type, in order.
    pub arms: Vec<MatchArm<T, Ty>>,
}

impl<T: Debug, Ty: Debug> Debug for MatchExpr<T, Ty> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.match_term.fmt(f)?;
        f.write_str(".{")?;
        for (arm_idx, arm) in self.arms.iter().enumerate() {
            if arm_idx > 0 {
                f.write_str("||")?;
            }
            write!(f, " #{arm_idx}")?;
            arm.fmt(f)?;
            write!(f, " ")?;
        }
        f.write_str("}")
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct MatchArm<T, Ty> {
    // A type expression within the context of one parameter of type `match_term.ty`. When that
    // parameter is substituted with `match_term.value`, the result must be the type of the match
    // expression. The type of `value`, then, is given by simultaneously weakening `motive`
    // according to the constructor parameters and substituting the implicit parameter with the
    // resulting constructor term.
    pub motive: Ty,

    // The value when matching against one particular constructor. Must be parameterized
    // equivalently to the constructor.
    pub value: Parameterized<T>,
}

impl<T: Debug, Ty: Debug> Debug for MatchArm<T, Ty> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Param::dbg_fmt_args(&self.value.params, f)?;
        f.write_str(" ↦ ")?;
        self.value.inner.fmt(f)?;
        if size_of::<Ty>() > 0 {
            f.write_str(" : [")?;
            self.motive.fmt(f)?;
            f.write_str("]")?;
        }
        let mut param_iter = self.value.params.iter();
        if let Some(param) = param_iter.next() {
            f.write_str(" | ")?;
            param.fmt(f)?;
            while let Some(param) = param_iter.next() {
                f.write_str("; ")?;
                param.fmt(f)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct ProjExpr {
    // The term to match on, whose type must reduce to a data type definition with exactly one
    // constructor and no custom equality definition.
    pub match_term: TypedExpr<TermExpr, TypeExpr>,

    // A reference to a constructor parameter with arguments.
    pub proj: VarExpr,
}

impl Debug for ProjExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.match_term.fmt(f)?;
        f.write_str(".")?;
        self.proj.fmt(f)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum TypeExpr {
    Base(BaseExpr<TypeExpr, ()>),

    // Data type definition.
    Data(DataType),
}

impl TypeExpr {
    pub const fn var(idx: ParamIdx) -> Self {
        TypeExpr::Base(BaseExpr::Var(VarExpr::new(idx)))
    }

    pub const fn fun(idx: ParamIdx, args: Vec<Arg>) -> Self {
        TypeExpr::Base(BaseExpr::Var(VarExpr { idx, args }))
    }
}

impl Default for TypeExpr {
    fn default() -> Self {
        TypeExpr::Base(BaseExpr::default())
    }
}

impl Debug for TypeExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TypeExpr::Base(base_expr) => base_expr.fmt(f),
            TypeExpr::Data(data_type) => data_type.fmt(f),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct DataType {
    pub ctors: Vec<Ctor>,
}

impl Debug for DataType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str("{")?;
        for (ctor_idx, ctor) in self.ctors.iter().enumerate() {
            if ctor_idx > 0 {
                f.write_str("||")?;
            }
            write!(f, " ")?;
            ctor.fmt(f)?;
            write!(f, " ")?;
        }
        f.write_str("}")
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Ctor {
    pub ident: Ident,
    pub ctor: Parameterized<()>,
}

impl Ctor {
    pub const fn new(ident: Ident, params: Vec<Param>) -> Self {
        Ctor {
            ident,
            ctor: Parameterized { params, inner: () },
        }
    }
}

impl Debug for Ctor {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.ident.fmt(f)?;
        Param::dbg_fmt_args(&self.ctor.params, f)?;
        let mut param_iter = self.ctor.params.iter();
        if let Some(param) = param_iter.next() {
            f.write_str(" | ")?;
            param.fmt(f)?;
            while let Some(param) = param_iter.next() {
                f.write_str("; ")?;
                param.fmt(f)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum TermExpr {
    Base(BaseExpr<TermExpr, TypeExpr>),

    // Constructor reference, where the constructor is treated like a global variable within the
    // context of the expression type.
    Ctor(VarExpr),

    // An explicit cast to a compatible type.
    Cast(Box<TypedExpr<TermExpr, TypeExpr>>),

    // A quoted type expression. As noted in the introduction, the parser simply produces an
    // expression in the outer context, and client code must reinterpret it in a quoted context, by
    // keeping all globals as-is and treating locals of type `Type` or `A.Inst` with `A : Type` as
    // antiquotations.
    QuotedType(Box<TypeExpr>),

    // A quoted term expression. As noted in the introduction, the parser simply produces an
    // expression in the outer context, and client code must reinterpret it in a quoted context, by
    // keeping all globals as-is and treating locals of type `Type` or `A.Inst` with `A : Type` as
    // antiquotations.
    QuotedTerm(Box<TermExpr>),
}

impl TermExpr {
    pub const fn var(idx: ParamIdx) -> Self {
        TermExpr::Base(BaseExpr::Var(VarExpr::new(idx)))
    }

    pub const fn fun(idx: ParamIdx, args: Vec<Arg>) -> Self {
        TermExpr::Base(BaseExpr::Var(VarExpr { idx, args }))
    }

    pub fn ctor(ctor_idx: usize, args: Vec<Arg>) -> Self {
        TermExpr::Ctor(VarExpr {
            idx: ctor_idx as ParamIdx,
            args,
        })
    }
}

impl Default for TermExpr {
    fn default() -> Self {
        TermExpr::Base(BaseExpr::default())
    }
}

impl Debug for TermExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TermExpr::Base(base_expr) => base_expr.fmt(f),
            TermExpr::Ctor(ctor_expr) => {
                f.write_str("_.")?;
                ctor_expr.fmt(f)
            }
            TermExpr::Cast(cast_expr) => cast_expr.fmt(f),
            TermExpr::QuotedType(ty) => {
                f.write_str("⌜")?;
                ty.fmt(f)?;
                f.write_str("⌝")
            }
            TermExpr::QuotedTerm(term) => {
                f.write_str("⌜")?;
                term.fmt(f)?;
                f.write_str("⌝")
            }
        }
    }
}

pub type Result<T> = std::result::Result<T, String>; // TODO: result enum

impl ContextObject for Param {
    fn weaken(&mut self, offset: usize) {
        todo!()
    }

    fn weakened(&self, offset: usize) -> Self {
        todo!()
    }

    fn map_subst<'a, Src: ToOwned>(
        src: CtxCow<'a, Parameterized<Src>>,
        project: impl FnOnce(Cow<'a, Src>) -> CtxCow<'a, Self>,
        args: CtxCow<'a, [Arg]>,
    ) -> CtxCow<'a, Self> {
        todo!()
    }
}

impl TypeExpr {
    pub fn reduce_head<'a>(&mut self, ctx: &Context<'a>) -> Result<bool> {
        let result = self.reduce_head_once(ctx)?;
        if result {
            while self.reduce_head_once(ctx)? {}
        }
        Ok(result)
    }

    fn reduce_head_once<'a>(&mut self, ctx: &Context<'a>) -> Result<bool> {
        todo!()
    }
}

impl ContextObject for TypeExpr {
    fn weaken(&mut self, offset: usize) {
        todo!()
    }

    fn weakened(&self, offset: usize) -> Self {
        todo!()
    }

    fn map_subst<'a, Src: ToOwned>(
        src: CtxCow<'a, Parameterized<Src>>,
        project: impl FnOnce(Cow<'a, Src>) -> CtxCow<'a, Self>,
        args: CtxCow<'a, [Arg]>,
    ) -> CtxCow<'a, Self> {
        todo!()
    }
}

impl TermExpr {
    pub fn reduce<'a>(&mut self, ctx: &Context<'a>) -> Result<bool> {
        todo!()
    }

    pub fn reduce_head<'a>(&mut self, ctx: &Context<'a>) -> Result<bool> {
        let result = self.reduce_head_once(ctx)?;
        if result {
            while self.reduce_head_once(ctx)? {}
        }
        Ok(result)
    }

    fn reduce_head_once<'a>(&mut self, ctx: &Context<'a>) -> Result<bool> {
        match self {
            TermExpr::Base(BaseExpr::Placeholder) => Ok(false),
            TermExpr::Base(BaseExpr::Var(var_expr)) => {
                let param = ctx.param(var_expr.idx);
                let content = param.project(|param| match param {
                    Cow::Borrowed(param) => Cow::Borrowed(&param.content),
                    Cow::Owned(param) => Cow::Owned(param.content),
                });
                if let ParamContent::Term { def: Some(_), .. } = &content.as_ref().value.inner {
                    let def = TermExpr::map_subst(
                        content,
                        |content| match content {
                            Cow::Borrowed(content) => {
                                let ParamContent::Term { def: Some(def), .. } = content else {
                                    unreachable!()
                                };
                                CtxCow::borrowed(def)
                            }
                            Cow::Owned(content) => {
                                let ParamContent::Term { def: Some(def), .. } = content else {
                                    unreachable!()
                                };
                                CtxCow::owned(def)
                            }
                        },
                        CtxCow::borrowed(&var_expr.args),
                    );
                    *self = def.into_owned();
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            TermExpr::Base(BaseExpr::Let(let_expr)) => todo!(),
            TermExpr::Base(BaseExpr::Match(match_expr)) => todo!(),
            TermExpr::Base(BaseExpr::Proj(proj_expr)) => todo!(),
            TermExpr::Ctor(_) => Ok(false),
            TermExpr::Cast(cast_expr) => todo!(),
            TermExpr::QuotedType(ty) => {
                // We can directly handle locals (which must necessarily be antiquotations) and
                // explicit data type definitions.
                match ty.as_mut() {
                    TypeExpr::Base(BaseExpr::Placeholder) => Ok(false),
                    TypeExpr::Base(BaseExpr::Var(var_expr)) if !var_expr.is_global() => {
                        if !var_expr.args.is_empty() {
                            todo!();
                        }
                        *self = TermExpr::Base(BaseExpr::Var(replace(var_expr, VarExpr::new(0))));
                        Ok(true)
                    }
                    TypeExpr::Data(data_type) => {
                        let meta_globals = ctx.meta_globals();
                        *self = meta_globals
                            .quote_data_type(replace(data_type, DataType { ctors: Vec::new() }))
                            .into_quoted_type_expr(meta_globals);
                        Ok(true)
                    }
                    ty => {
                        // Otherwise, head-reducing `ty` could help. However, `ctx` is not the right
                        // context for this reduction, as the types of all locals would be wrong. So
                        // we create a wrapper context that just maps the types of all potential
                        // antiquotations.
                        ty.reduce_head(&ctx.quoted())
                    }
                }
            }
            TermExpr::QuotedTerm(term) => {
                // We can directly handle locals (which must necessarily be antiquotations) and
                // constructor terms.
                match term.as_mut() {
                    TermExpr::Base(BaseExpr::Placeholder) => Ok(false),
                    TermExpr::Base(BaseExpr::Var(var_expr)) if !var_expr.is_global() => {
                        if !var_expr.args.is_empty() {
                            todo!();
                        }
                        *self = TermExpr::Base(BaseExpr::Var(replace(var_expr, VarExpr::new(0))));
                        Ok(true)
                    }
                    TermExpr::Ctor(ctor_expr) => todo!(),
                    term => {
                        // Otherwise, head-reducing `term` could help. However, `ctx` is not the
                        // right context for this reduction, as the types of all locals would be
                        // wrong. So we create a wrapper context that just maps the types of all
                        // potential antiquotations.
                        term.reduce_head(&ctx.quoted())
                    }
                }
            }
        }
    }
}

impl ContextObject for TermExpr {
    fn weaken(&mut self, offset: usize) {
        todo!()
    }

    fn weakened(&self, offset: usize) -> Self {
        todo!()
    }

    fn map_subst<'a, Src: ToOwned>(
        src: CtxCow<'a, Parameterized<Src>>,
        project: impl FnOnce(Cow<'a, Src>) -> CtxCow<'a, Self>,
        args: CtxCow<'a, [Arg]>,
    ) -> CtxCow<'a, Self> {
        todo!()
    }
}
