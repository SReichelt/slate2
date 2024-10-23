// The expressions defined here reflect what the parser produces based on the information available
// to it. In particular, terms are not necessarily well-typed because the parser cannot perform full
// type computation. Moreover, quoted expressions are parsed in the surrounding context, even though
// most variables from that context are not valid antiquotations.
//
// The code relies on parameters and arguments fitting together, and on constructors fitting the
// expected data types, but not on well-typedness of terms in general. To interpret a given term, it
// is often necessary to know its type.

// Some thoughts on how to implement equality:
//
// Probably the most central building block of the entire proof assistant implementation is the
// substitution mechanism, which can be thought of as an implementation of meta-level functions,
// i.e. it is the mechanism "below" HOAS. We require these functions to respect object-level
// equality/equivalence (where equality may be dependent over an equivalence!), and in fact the
// `«_»` mechanism makes this requirement explicit at the object level.
//
// So ultimately we need an extended substitution mechanism which, for each regular type or term
// argument, alternatively accepts a pair of such arguments together with an appropriate equality
// term (i.e. an "interval", basically), and outputs the same kind of triple of the resulting
// object, whatever that means for that type of object. (The equality in the result should probably
// always be a term, not a Rust object, as we may need to perform the same kind of substitution on
// it in a recursive fashion.)
//
// One interesting aspect of this mechanism is that substitution of the two endpoints happens
// during type reduction, whereas substitution of the equality happens during term reduction.
// Therefore, it would not make sense to combine these substitutions, and in fact the substitution
// of the endpoints can use the existing mechanism unmodified.
//
// Regarding the different kinds of expressions:
//
// * Variable references need to support the `«_»` mechanism (also recursively, probably), and this
//   mechanism is also used recusively to implement equality substitution.
//   Parameterized arguments are an interesting topic, as the parameter type can be different for
//   the two endpoints of an input equality/equivalence. In such a case, we probably want to resort
//   to `%any` or `%Any`, respectively, to convert that input equality/equivalence back to a single
//   instance/type.
//
// * Match expressions already contain the necessary equality mappings, but we need to construct
//   them automatically if they are not user-defined.
//   We have to be careful not to assume that applying `refl` will always result literally in
//   `refl`.
//
// * For a data type definition, we need to construct an instance of the corresponding equivalence.
//   The resulting functions match on their arguments and produce an instance of the same
//   constructor in the other data type.
//
// * Equality types are interesting because it seems that substituting in these types is really what
//   defines the axioms of equality.

// Some thoughts on universes:
//
// For ergonomic reasons, we probably want to keep using `%Type` even in constructor arguments.
// We could say that this makes data types universe-polymorphic, but we need to figure out a good
// way to specify universes explicitly when we want to talk about relationships between them (e.g.
// an ordinal of all ordinals in a specific universe). One way to solve this would be via a cast of
// the data type into a universe (e.g. going from `Ord %Type` to `Ord : U`). This would cause the
// target universe to restrict which instances of the data type are valid at that point.

use std::{
    borrow::Cow,
    fmt::{self, Debug, Formatter},
    mem::{replace, take},
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

impl<T: ContextObject<Owned = T> + Clone> ContextObject for Parameterized<T> {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        if weaken_by != 0 {
            self.params.weaken(offset, weaken_by);
            self.inner.weaken(offset + self.params.len(), weaken_by);
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> <Self as ToOwned>::Owned {
        Parameterized {
            params: self.params.weakened(offset, weaken_by),
            inner: self.inner.weakened(offset + self.params.len(), weaken_by),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        self.params
            .subst_impl(offset, params.as_borrowed(), args.as_borrowed());
        self.inner
            .subst_impl(offset + self.params.len(), params, args);
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

    fn extract_one(params: CtxCow<'_, [Self]>, idx: usize, prev_args: CtxCow<'_, [Arg]>) -> Self {
        let (prev_params, mut param) = match params {
            CtxCow::Borrowed(params) => (
                CtxCow::Borrowed(CtxRef {
                    value: &params.value[..idx],
                    weaken_by: params.weaken_by,
                }),
                params.value[idx].weakened(idx, params.weaken_by),
            ),
            CtxCow::Owned(mut params) => {
                params.truncate(idx + 1);
                let param = params.pop().unwrap();
                (CtxCow::Owned(params), param)
            }
        };
        param.subst_impl(0, prev_params, prev_args);
        param
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

impl ContextObject for Param {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        self.content.weaken(offset, weaken_by)
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        Param {
            ident: self.ident.clone(),
            content: self.content.weakened(offset, weaken_by),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        self.content.subst_impl(offset, params, args)
    }
}

impl ContextObject for [Param] {
    fn weaken(&mut self, mut offset: CtxOffset, weaken_by: CtxOffset) {
        for param in self {
            param.weaken(offset, weaken_by);
            offset += 1;
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self::Owned {
        self.iter()
            .enumerate()
            .map(|(idx, param)| param.weakened(offset + idx, weaken_by))
            .collect()
    }

    fn subst_impl(
        &mut self,
        mut offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        let mut iter = self.iter_mut();
        if let Some(next_param) = iter.next() {
            let mut param = next_param;
            loop {
                if let Some(next_param) = iter.next() {
                    param.subst_impl(offset, params.as_borrowed(), args.as_borrowed());
                    offset += 1;
                    param = next_param;
                } else {
                    // Optimization: move instead of borrowing.
                    param.subst_impl(offset, params, args);
                    return;
                }
            }
        }
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

impl ContextObject for ParamContent {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        match self {
            ParamContent::Type { def } => def.weaken(offset, weaken_by),
            ParamContent::Term { ty, def } => {
                ty.weaken(offset, weaken_by);
                def.weaken(offset, weaken_by);
            }
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        match self {
            ParamContent::Type { def } => ParamContent::Type {
                def: def.weakened(offset, weaken_by),
            },
            ParamContent::Term { ty, def } => ParamContent::Term {
                ty: ty.weakened(offset, weaken_by),
                def: def.weakened(offset, weaken_by),
            },
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        match self {
            ParamContent::Type { def } => def.subst_impl(offset, params, args),
            ParamContent::Term { ty, def } => {
                def.subst_impl(offset, params.as_borrowed(), args.as_borrowed());
                ty.subst_impl(offset, params, args);
            }
        }
    }
}

/// An argument corresponding to a given `Param`.
#[derive(Clone, PartialEq, Eq)]
pub struct Arg {
    /// The type or term (depending on the param), parameterized equivalently to the param. `None` if
    /// the param is a definition.
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

impl ContextObject for Arg {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        self.value.weaken(offset, weaken_by)
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        Arg {
            value: self.value.weakened(offset, weaken_by),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        self.value.subst_impl(offset, params, args)
    }
}

impl ContextObject for [Arg] {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        for arg in self {
            arg.weaken(offset, weaken_by);
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self::Owned {
        self.iter()
            .map(|arg| arg.weakened(offset, weaken_by))
            .collect()
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        let mut iter = self.iter_mut();
        if let Some(next_arg) = iter.next() {
            let mut arg = next_arg;
            loop {
                if let Some(next_arg) = iter.next() {
                    arg.subst_impl(offset, params.as_borrowed(), args.as_borrowed());
                    arg = next_arg;
                } else {
                    // Optimization: move instead of borrowing.
                    arg.subst_impl(offset, params, args);
                    return;
                }
            }
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

impl ContextObject for ArgValue {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        match self {
            ArgValue::Type(type_expr) => type_expr.weaken(offset, weaken_by),
            ArgValue::Term(term_expr) => term_expr.weaken(offset, weaken_by),
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        match self {
            ArgValue::Type(type_expr) => ArgValue::Type(type_expr.weakened(offset, weaken_by)),
            ArgValue::Term(term_expr) => ArgValue::Term(term_expr.weakened(offset, weaken_by)),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        match self {
            ArgValue::Type(type_expr) => type_expr.subst_impl(offset, params, args),
            ArgValue::Term(term_expr) => term_expr.subst_impl(offset, params, args),
        }
    }
}

pub trait Expr: Clone + PartialEq + Eq + Debug + ContextObject<Owned = Self> {
    type Ty: Expr;

    fn has_content() -> bool {
        true
    }
}

impl Expr for () {
    type Ty = ();

    fn has_content() -> bool {
        false
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum BaseExpr<T: Expr> {
    /// A placeholder or error expression that should be propagated as far as possible in order to
    /// produce more useful diagnostics.
    Placeholder,

    /// Variable reference, with exactly one arg per parameterization.
    Var(VarExpr),

    /// Let-binding. All params must be definitions.
    Let(Box<Parameterized<T>>),

    /// Matching on a term.
    Match(Box<MatchExpr<T>>),

    /// Projection, which is essentially a shorthand for matching on a single constructor.
    Proj(Box<ProjExpr>),
}

impl<T: Expr> Default for BaseExpr<T> {
    fn default() -> Self {
        BaseExpr::Placeholder
    }
}

impl<T: Expr> Debug for BaseExpr<T> {
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

impl<T: Expr> BaseExpr<T> {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        match self {
            BaseExpr::Placeholder => {}
            BaseExpr::Var(var_expr) => var_expr.weaken(offset, weaken_by),
            BaseExpr::Let(let_expr) => let_expr.weaken(offset, weaken_by),
            BaseExpr::Match(match_expr) => match_expr.weaken(offset, weaken_by),
            BaseExpr::Proj(proj_expr) => proj_expr.weaken(offset, weaken_by),
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        match self {
            BaseExpr::Placeholder => BaseExpr::Placeholder,
            BaseExpr::Var(var_expr) => BaseExpr::Var(var_expr.weakened(offset, weaken_by)),
            BaseExpr::Let(let_expr) => {
                BaseExpr::Let(Box::new(let_expr.weakened(offset, weaken_by)))
            }
            BaseExpr::Match(match_expr) => {
                BaseExpr::Match(Box::new(match_expr.weakened(offset, weaken_by)))
            }
            BaseExpr::Proj(proj_expr) => {
                BaseExpr::Proj(Box::new(proj_expr.weakened(offset, weaken_by)))
            }
        }
    }

    #[must_use]
    fn try_subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) -> Option<&mut VarExpr> {
        match self {
            BaseExpr::Placeholder => {}
            BaseExpr::Var(var_expr) => return var_expr.try_subst_impl(offset, params, args),
            BaseExpr::Let(let_expr) => let_expr.subst_impl(offset, params, args),
            BaseExpr::Match(match_expr) => match_expr.subst_impl(offset, params, args),
            BaseExpr::Proj(proj_expr) => proj_expr.subst_impl(offset, params, args),
        }
        None
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct VarExpr {
    /// The De Bruijn index or level of the referenced variable.
    pub idx: ParamIdx,

    /// One argument for each parameter of the referenced variable.
    pub args: Vec<Arg>,

    /// Specifies that the type of the referenced variable matches the expected type exactly, up to
    /// unfolding of definitions. Can be set to `true` by the type checker to optimize substitution,
    /// which needs to insert an explicit cast otherwise.
    pub ty_exact: bool,
}

impl VarExpr {
    pub const fn new(idx: ParamIdx) -> Self {
        VarExpr {
            idx,
            args: Vec::new(),
            ty_exact: false,
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

impl VarExpr {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        Self::weaken_idx(&mut self.idx, offset, weaken_by);
        self.args.weaken(offset, weaken_by);
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        let mut idx = self.idx;
        Self::weaken_idx(&mut idx, offset, weaken_by);
        VarExpr {
            idx,
            args: self.args.weakened(offset, weaken_by),
            ty_exact: self.ty_exact,
        }
    }

    fn weaken_idx(idx: &mut ParamIdx, offset: CtxOffset, weaken_by: CtxOffset) {
        if *idx < -(offset as ParamIdx) {
            *idx -= weaken_by as ParamIdx;
        }
    }

    #[must_use]
    fn try_subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) -> Option<&mut Self> {
        let params_len = params.len();
        self.args.subst_impl(offset, params, args);
        if self.idx < -(offset as ParamIdx) {
            if self.idx < -((offset + params_len) as ParamIdx) {
                self.idx += params_len as ParamIdx;
            } else {
                return Some(self);
            }
        }
        None
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct TypedExpr<T: Expr> {
    pub ty: T::Ty,
    pub value: T,
}

impl<T: Expr> Debug for TypedExpr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if T::Ty::has_content() {
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

impl<T: Expr> ContextObject for TypedExpr<T> {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        self.ty.weaken(offset, weaken_by);
        self.value.weaken(offset, weaken_by);
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        TypedExpr {
            ty: self.ty.weakened(offset, weaken_by),
            value: self.value.weakened(offset, weaken_by),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        self.ty
            .subst_impl(offset, params.as_borrowed(), args.as_borrowed());
        self.value.subst_impl(offset, params, args);
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct MatchExpr<T: Expr> {
    /// The term to match on, whose type must reduce to a data type definition.
    pub match_term: TypedExpr<TermExpr>,

    /// Exactly one arm for each constructor of the data type, in order.
    pub arms: Vec<MatchArm<T>>,
}

impl<T: Expr> Debug for MatchExpr<T> {
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

impl<T: Expr> ContextObject for MatchExpr<T> {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        self.match_term.weaken(offset, weaken_by);
        for arm in &mut self.arms {
            arm.weaken(offset, weaken_by);
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        MatchExpr {
            match_term: self.match_term.weakened(offset, weaken_by),
            arms: self
                .arms
                .iter()
                .map(|arm| arm.weakened(offset, weaken_by))
                .collect(),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        for arm in &mut self.arms {
            arm.subst_impl(offset, params.as_borrowed(), args.as_borrowed());
        }
        self.match_term.subst_impl(offset, params, args);
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct MatchArm<T: Expr> {
    /// A type expression within the context of one parameter of type `match_term.ty`. When that
    /// parameter is substituted with `match_term.value`, the result must be the type of the match
    /// expression. The type of `value`, then, is given by simultaneously weakening `motive`
    /// according to the constructor parameters and substituting the implicit parameter with the
    /// resulting constructor term.
    pub motive: T::Ty,

    /// The value when matching against one particular constructor. Must be parameterized
    /// equivalently to the constructor.
    pub value: Parameterized<T>,
}

impl<T: Expr> Debug for MatchArm<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Param::dbg_fmt_args(&self.value.params, f)?;
        f.write_str(" ↦ ")?;
        self.value.inner.fmt(f)?;
        if T::Ty::has_content() {
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

impl<T: Expr> ContextObject for MatchArm<T> {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        self.motive.weaken(offset + 1, weaken_by);
        self.value.weaken(offset, weaken_by);
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        MatchArm {
            motive: self.motive.weakened(offset + 1, weaken_by),
            value: self.value.weakened(offset, weaken_by),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        self.motive
            .subst_impl(offset + 1, params.as_borrowed(), args.as_borrowed());
        self.value.subst_impl(offset, params, args);
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct ProjExpr {
    /// The term to match on, whose type must reduce to a data type definition with exactly one
    /// constructor and no custom equality definition.
    pub match_term: TypedExpr<TermExpr>,

    /// A reference to a constructor parameter with arguments.
    pub proj: VarExpr,
}

impl Debug for ProjExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.match_term.fmt(f)?;
        f.write_str(".")?;
        self.proj.fmt(f)
    }
}

impl ContextObject for ProjExpr {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        self.match_term.weaken(offset, weaken_by);
        self.proj.args.weaken(offset, weaken_by);
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        ProjExpr {
            match_term: self.match_term.weakened(offset, weaken_by),
            proj: VarExpr {
                idx: self.proj.idx,
                args: self.proj.args.weakened(offset, weaken_by),
                ty_exact: self.proj.ty_exact,
            },
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        self.match_term
            .subst_impl(offset, params.as_borrowed(), args.as_borrowed());
        self.proj.args.subst_impl(offset, params, args);
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum TypeExpr {
    Base(BaseExpr<TypeExpr>),

    /// Data type definition.
    Data(DataType),
}

impl TypeExpr {
    pub const fn var(idx: ParamIdx) -> Self {
        TypeExpr::Base(BaseExpr::Var(VarExpr::new(idx)))
    }

    pub const fn fun(idx: ParamIdx, args: Vec<Arg>) -> Self {
        TypeExpr::Base(BaseExpr::Var(VarExpr {
            idx,
            args,
            ty_exact: false,
        }))
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

impl ContextObject for TypeExpr {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        match self {
            TypeExpr::Base(base_expr) => base_expr.weaken(offset, weaken_by),
            TypeExpr::Data(data_type) => data_type.weaken(offset, weaken_by),
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        match self {
            TypeExpr::Base(base_expr) => TypeExpr::Base(base_expr.weakened(offset, weaken_by)),
            TypeExpr::Data(data_type) => TypeExpr::Data(data_type.weakened(offset, weaken_by)),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        match self {
            TypeExpr::Base(base_expr) => {
                if let Some(var_expr) =
                    base_expr.try_subst_impl(offset, params.as_borrowed(), args.as_borrowed())
                {
                    let idx = (var_expr.idx + ((offset + params.len()) as ParamIdx)) as usize;
                    let (prev_args, arg) = args.project_idx(idx);
                    if let Some(mut arg_value) = arg
                        .project(|arg| match arg {
                            Cow::Borrowed(arg) => Cow::Borrowed(&arg.value),
                            Cow::Owned(arg) => Cow::Owned(arg.value),
                        })
                        .as_option()
                    {
                        arg_value.weaken(offset);
                        let ArgValue::Type(ty) =
                            ArgValue::subst(arg_value, CtxCow::Owned(take(&mut var_expr.args)))
                                .into_owned()
                        else {
                            panic!("expected type argument");
                        };
                        *self = ty;
                    } else {
                        let param = Param::extract_one(params, idx, prev_args);
                        let ParamContent::Type { def: Some(def) } = ParamContent::subst(
                            CtxCow::Owned(param.content),
                            CtxCow::Owned(take(&mut var_expr.args)),
                        )
                        .into_owned() else {
                            panic!("expected type definition");
                        };
                        *self = def;
                    }
                }
            }
            TypeExpr::Data(data_type) => data_type.subst_impl(offset, params, args),
        }
    }
}

impl Expr for TypeExpr {
    type Ty = ();
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

impl ContextObject for DataType {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        for ctor in &mut self.ctors {
            ctor.weaken(offset, weaken_by);
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        DataType {
            ctors: self
                .ctors
                .iter()
                .map(|ctor| ctor.weakened(offset, weaken_by))
                .collect(),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        let mut iter = self.ctors.iter_mut();
        if let Some(next_ctor) = iter.next() {
            let mut ctor = next_ctor;
            loop {
                if let Some(next_ctor) = iter.next() {
                    ctor.subst_impl(offset, params.as_borrowed(), args.as_borrowed());
                    ctor = next_ctor;
                } else {
                    // Optimization: move instead of borrowing.
                    ctor.subst_impl(offset, params, args);
                    return;
                }
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Ctor {
    pub ident: Ident,
    pub params: Vec<Param>,
}

impl Ctor {
    pub const fn new(ident: Ident, params: Vec<Param>) -> Self {
        Ctor { ident, params }
    }
}

impl Debug for Ctor {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.ident.fmt(f)?;
        Param::dbg_fmt_args(&self.params, f)?;
        let mut param_iter = self.params.iter();
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

impl ContextObject for Ctor {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        self.params.weaken(offset, weaken_by)
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        Ctor {
            ident: self.ident.clone(),
            params: self.params.weakened(offset, weaken_by),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        self.params.subst_impl(offset, params, args)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum TermExpr {
    Base(BaseExpr<TermExpr>),

    /// Constructor reference, where the constructor is treated like a global variable within the
    /// context of the expression type.
    Ctor(CtorExpr),

    /// An explicit cast to a compatible type.
    Cast(Box<TypedExpr<TermExpr>>),

    /// A quoted type expression. As noted in the introduction, the parser simply produces an
    /// expression in the outer context, and client code must reinterpret it in a quoted context, by
    /// keeping all globals as-is and treating locals of type `Type` or `A.Inst` with `A : Type` as
    /// antiquotations.
    QuotedType(Box<TypeExpr>),

    /// A quoted term expression. As noted in the introduction, the parser simply produces an
    /// expression in the outer context, and client code must reinterpret it in a quoted context, by
    /// keeping all globals as-is and treating locals of type `Type` or `A.Inst` with `A : Type` as
    /// antiquotations.
    QuotedTerm(Box<TermExpr>),
}

impl TermExpr {
    pub const fn var(idx: ParamIdx) -> Self {
        TermExpr::Base(BaseExpr::Var(VarExpr::new(idx)))
    }

    pub const fn fun(idx: ParamIdx, args: Vec<Arg>) -> Self {
        TermExpr::Base(BaseExpr::Var(VarExpr {
            idx,
            args,
            ty_exact: false,
        }))
    }

    pub const fn ctor(idx: usize, args: Vec<Arg>) -> Self {
        TermExpr::Ctor(CtorExpr { idx, args })
    }

    pub fn cast(ty: TypeExpr, term: TermExpr) -> Self {
        TermExpr::Cast(Box::new(TypedExpr { ty, value: term }))
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

impl ContextObject for TermExpr {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        match self {
            TermExpr::Base(base_expr) => base_expr.weaken(offset, weaken_by),
            TermExpr::Ctor(ctor_expr) => ctor_expr.weaken(offset, weaken_by),
            TermExpr::Cast(cast_expr) => cast_expr.weaken(offset, weaken_by),
            TermExpr::QuotedType(ty) => ty.weaken(offset, weaken_by),
            TermExpr::QuotedTerm(term) => term.weaken(offset, weaken_by),
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        match self {
            TermExpr::Base(base_expr) => TermExpr::Base(base_expr.weakened(offset, weaken_by)),
            TermExpr::Ctor(ctor_expr) => TermExpr::Ctor(ctor_expr.weakened(offset, weaken_by)),
            TermExpr::Cast(cast_expr) => {
                TermExpr::Cast(Box::new(cast_expr.weakened(offset, weaken_by)))
            }
            TermExpr::QuotedType(ty) => {
                TermExpr::QuotedType(Box::new(ty.weakened(offset, weaken_by)))
            }
            TermExpr::QuotedTerm(term) => {
                TermExpr::QuotedTerm(Box::new(term.weakened(offset, weaken_by)))
            }
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        match self {
            TermExpr::Base(base_expr) => {
                if let Some(var_expr) =
                    base_expr.try_subst_impl(offset, params.as_borrowed(), args.as_borrowed())
                {
                    let idx = (var_expr.idx + ((offset + params.len()) as ParamIdx)) as usize;
                    let (prev_args, arg) = args.project_idx(idx);
                    if let Some(mut arg_value) = arg
                        .project(|arg| match arg {
                            Cow::Borrowed(arg) => Cow::Borrowed(&arg.value),
                            Cow::Owned(arg) => Cow::Owned(arg.value),
                        })
                        .as_option()
                    {
                        arg_value.weaken(offset);
                        let mut cast_ty = None;
                        if !var_expr.ty_exact {
                            let param = Param::extract_one(params, idx, prev_args);
                            let ParamContent::Term { ty, def: None } = ParamContent::subst(
                                CtxCow::Owned(param.content),
                                CtxCow::borrowed(&var_expr.args),
                            )
                            .into_owned() else {
                                panic!("term argument for non-term parameter");
                            };
                            cast_ty = Some(ty);
                        }
                        let ArgValue::Term(mut term) =
                            ArgValue::subst(arg_value, CtxCow::Owned(take(&mut var_expr.args)))
                                .into_owned()
                        else {
                            panic!("expected term argument");
                        };
                        if let Some(ty) = cast_ty {
                            term = TermExpr::cast(ty, term);
                        }
                        *self = term;
                    } else {
                        let param = Param::extract_one(params, idx, prev_args);
                        let ParamContent::Term {
                            ty,
                            def: Some(mut def),
                        } = ParamContent::subst(
                            CtxCow::Owned(param.content),
                            CtxCow::Owned(take(&mut var_expr.args)),
                        )
                        .into_owned()
                        else {
                            panic!("expected term definition");
                        };
                        if !var_expr.ty_exact {
                            def = TermExpr::cast(ty, def);
                        }
                        *self = def;
                    }
                }
            }
            TermExpr::Ctor(ctor_expr) => ctor_expr.subst_impl(offset, params, args),
            TermExpr::Cast(cast_expr) => cast_expr.subst_impl(offset, params, args),
            TermExpr::QuotedType(ty) => ty.subst_impl(offset, params, args),
            TermExpr::QuotedTerm(term) => term.subst_impl(offset, params, args),
        }
    }
}

impl Expr for TermExpr {
    type Ty = TypeExpr;
}

#[derive(Clone, PartialEq, Eq)]
pub struct CtorExpr {
    /// The index of the constructor within the data type.
    pub idx: usize,

    /// One argument for each parameter of the constructor.
    pub args: Vec<Arg>,
}

impl Debug for CtorExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.idx)?;
        Arg::dbg_fmt_args(&self.args, f)
    }
}

impl ContextObject for CtorExpr {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        self.args.weaken(offset, weaken_by);
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self {
        CtorExpr {
            idx: self.idx,
            args: self.args.weakened(offset, weaken_by),
        }
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        self.args.subst_impl(offset, params, args);
    }
}

pub type Result<T> = std::result::Result<T, String>; // TODO: result enum

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
                                Cow::Borrowed(def)
                            }
                            Cow::Owned(content) => {
                                let ParamContent::Term { def: Some(def), .. } = content else {
                                    unreachable!()
                                };
                                Cow::Owned(def)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subst_ty_plain() {
        let input = Parameterized {
            params: vec![Param::ty(Ident::new("A"))],
            inner: TypeExpr::fun(-2, vec![Arg::ty(TypeExpr::var(-1))]),
        };
        let output = TypeExpr::subst(
            CtxCow::Owned(input),
            CtxCow::Owned(vec![Arg::ty(TypeExpr::var(-42))]),
        );
        assert_eq!(
            output.into_owned(),
            TypeExpr::fun(-1, vec![Arg::ty(TypeExpr::var(-42))])
        );
    }

    #[test]
    fn subst_ty_fun_and_args() {
        let input = Parameterized {
            params: vec![
                Param {
                    ident: Ident::new("F"),
                    content: Parameterized {
                        params: vec![Param::ty(Ident::new("A")), Param::ty(Ident::new("B"))],
                        inner: ParamContent::ty(),
                    },
                },
                Param::ty(Ident::new("C")),
            ],
            inner: TypeExpr::fun(
                -2,
                vec![
                    Arg::ty(TypeExpr::fun(
                        -2,
                        vec![Arg::ty(TypeExpr::var(-23)), Arg::ty(TypeExpr::var(-1))],
                    )),
                    Arg::ty(TypeExpr::var(-1)),
                ],
            ),
        };
        let output = TypeExpr::subst(
            CtxCow::Owned(input),
            CtxCow::Owned(vec![
                Arg {
                    value: Some(Parameterized {
                        params: vec![Param::ty(Ident::new("A")), Param::ty(Ident::new("B"))],
                        inner: ArgValue::Type(TypeExpr::fun(
                            -37,
                            vec![Arg::ty(TypeExpr::var(-1)), Arg::ty(TypeExpr::var(-2))],
                        )),
                    }),
                },
                Arg::ty(TypeExpr::var(-42)),
            ]),
        );
        assert_eq!(
            output.into_owned(),
            TypeExpr::fun(
                -35,
                vec![
                    Arg::ty(TypeExpr::var(-42)),
                    Arg::ty(TypeExpr::fun(
                        -35,
                        vec![Arg::ty(TypeExpr::var(-42)), Arg::ty(TypeExpr::var(-21))]
                    )),
                ]
            )
        );
    }

    #[test]
    fn subst_ty_higher_order() {
        let input = Parameterized {
            params: vec![Param {
                ident: Ident::new("F"),
                content: Parameterized {
                    params: vec![
                        Param::ty(Ident::new("A")),
                        Param {
                            ident: Ident::new("G"),
                            content: Parameterized {
                                params: vec![
                                    Param::ty(Ident::new("B")),
                                    Param::ty(Ident::new("C")),
                                ],
                                inner: ParamContent::ty(),
                            },
                        },
                    ],
                    inner: ParamContent::ty(),
                },
            }],
            inner: TypeExpr::fun(
                -1,
                vec![
                    Arg::ty(TypeExpr::var(-24)),
                    Arg {
                        value: Some(Parameterized {
                            params: vec![Param::ty(Ident::new("B")), Param::ty(Ident::new("C"))],
                            inner: ArgValue::Type(TypeExpr::fun(
                                -45,
                                vec![
                                    Arg::ty(TypeExpr::var(-1)),
                                    Arg::ty(TypeExpr::fun(
                                        -3,
                                        vec![
                                            Arg::ty(TypeExpr::var(-26)),
                                            Arg {
                                                value: Some(Parameterized {
                                                    params: vec![
                                                        Param::ty(Ident::new("C")),
                                                        Param::ty(Ident::new("B")),
                                                    ],
                                                    inner: ArgValue::Type(TypeExpr::fun(
                                                        -47,
                                                        vec![
                                                            Arg::ty(TypeExpr::var(-1)),
                                                            Arg::ty(TypeExpr::var(-2)),
                                                        ],
                                                    )),
                                                }),
                                            },
                                        ],
                                    )),
                                ],
                            )),
                        }),
                    },
                ],
            ),
        };
        let output = TypeExpr::subst(
            CtxCow::Owned(input),
            CtxCow::Owned(vec![Arg {
                value: Some(Parameterized {
                    params: vec![
                        Param::ty(Ident::new("A")),
                        Param {
                            ident: Ident::new("G"),
                            content: Parameterized {
                                params: vec![
                                    Param::ty(Ident::new("B")),
                                    Param::ty(Ident::new("C")),
                                ],
                                inner: ParamContent::ty(),
                            },
                        },
                    ],
                    inner: ArgValue::Type(TypeExpr::fun(
                        -1,
                        vec![Arg::ty(TypeExpr::var(-2)), Arg::ty(TypeExpr::var(-37))],
                    )),
                }),
            }]),
        );
        assert_eq!(
            output.into_owned(),
            TypeExpr::fun(
                -42,
                vec![
                    Arg::ty(TypeExpr::var(-35)),
                    Arg::ty(TypeExpr::fun(
                        -42,
                        vec![Arg::ty(TypeExpr::var(-35)), Arg::ty(TypeExpr::var(-23))]
                    )),
                ]
            )
        );
    }

    #[test]
    fn subst_ty_def() {
        let input = Parameterized {
            params: vec![
                Param::ty(Ident::new("A")),
                Param {
                    ident: Ident::new("F"),
                    content: Parameterized {
                        params: vec![Param::ty(Ident::new("B")), Param::ty(Ident::new("C"))],
                        inner: ParamContent::ty(),
                    },
                },
                Param {
                    ident: Ident::new("D"),
                    content: Parameterized::new(ParamContent::Type {
                        def: Some(TypeExpr::fun(
                            -1,
                            vec![Arg::ty(TypeExpr::var(-2)), Arg::ty(TypeExpr::var(-2))],
                        )),
                    }),
                },
                Param::ty(Ident::new("E")),
            ],
            inner: TypeExpr::fun(
                -3,
                vec![Arg::ty(TypeExpr::var(-2)), Arg::ty(TypeExpr::var(-1))],
            ),
        };
        let output = TypeExpr::subst(
            CtxCow::Owned(input),
            CtxCow::Owned(vec![
                Arg::ty(TypeExpr::var(-42)),
                Arg {
                    value: Some(Parameterized {
                        params: vec![Param::ty(Ident::new("B")), Param::ty(Ident::new("C"))],
                        inner: ArgValue::Type(TypeExpr::fun(
                            -25,
                            vec![Arg::ty(TypeExpr::var(-2)), Arg::ty(TypeExpr::var(-1))],
                        )),
                    }),
                },
                Arg::def(),
                Arg::ty(TypeExpr::var(-35)),
            ]),
        );
        assert_eq!(
            output.into_owned(),
            TypeExpr::fun(
                -23,
                vec![
                    Arg::ty(TypeExpr::fun(
                        -23,
                        vec![Arg::ty(TypeExpr::var(-42)), Arg::ty(TypeExpr::var(-42))]
                    )),
                    Arg::ty(TypeExpr::var(-35)),
                ]
            )
        );
    }

    #[test]
    fn subst_ty_fun_def() {
        let input = Parameterized {
            params: vec![
                Param::ty(Ident::new("A")),
                Param {
                    ident: Ident::new("F"),
                    content: Parameterized {
                        params: vec![Param::ty(Ident::new("B")), Param::ty(Ident::new("C"))],
                        inner: ParamContent::ty(),
                    },
                },
                Param {
                    ident: Ident::new("G"),
                    content: Parameterized {
                        params: vec![Param::ty(Ident::new("C")), Param::ty(Ident::new("B"))],
                        inner: ParamContent::Type {
                            def: Some(TypeExpr::fun(
                                -3,
                                vec![Arg::ty(TypeExpr::var(-1)), Arg::ty(TypeExpr::var(-2))],
                            )),
                        },
                    },
                },
                Param::ty(Ident::new("E")),
            ],
            inner: TypeExpr::fun(
                -2,
                vec![Arg::ty(TypeExpr::var(-4)), Arg::ty(TypeExpr::var(-1))],
            ),
        };
        let output = TypeExpr::subst(
            CtxCow::Owned(input),
            CtxCow::Owned(vec![
                Arg::ty(TypeExpr::var(-42)),
                Arg {
                    value: Some(Parameterized {
                        params: vec![Param::ty(Ident::new("B")), Param::ty(Ident::new("C"))],
                        inner: ArgValue::Type(TypeExpr::fun(
                            -25,
                            vec![Arg::ty(TypeExpr::var(-2)), Arg::ty(TypeExpr::var(-1))],
                        )),
                    }),
                },
                Arg::def(),
                Arg::ty(TypeExpr::var(-35)),
            ]),
        );
        assert_eq!(
            output.into_owned(),
            TypeExpr::fun(
                -23,
                vec![Arg::ty(TypeExpr::var(-35)), Arg::ty(TypeExpr::var(-42)),]
            )
        );
    }

    #[test]
    fn subst_term_plain() {
        let input = Parameterized {
            params: vec![Param::term(Ident::new("a"), TypeExpr::var(-23))],
            inner: TermExpr::fun(-2, vec![Arg::term(TermExpr::var(-1))]),
        };
        let output = TermExpr::subst(
            CtxCow::Owned(input),
            CtxCow::Owned(vec![Arg::term(TermExpr::var(-42))]),
        );
        assert_eq!(
            output.into_owned(),
            TermExpr::fun(
                -1,
                vec![Arg::term(TermExpr::cast(
                    TypeExpr::var(-23),
                    TermExpr::var(-42)
                ))]
            )
        );
    }

    #[test]
    fn subst_ty_term_plain() {
        let input = Parameterized {
            params: vec![
                Param::ty(Ident::new("A")),
                Param::term(Ident::new("a"), TypeExpr::var(-1)),
            ],
            inner: TermExpr::fun(-3, vec![Arg::term(TermExpr::var(-1))]),
        };
        let output = TermExpr::subst(
            CtxCow::Owned(input),
            CtxCow::Owned(vec![
                Arg::ty(TypeExpr::var(-23)),
                Arg::term(TermExpr::var(-42)),
            ]),
        );
        assert_eq!(
            output.into_owned(),
            TermExpr::fun(
                -1,
                vec![Arg::term(TermExpr::cast(
                    TypeExpr::var(-23),
                    TermExpr::var(-42)
                ))]
            )
        );
    }

    #[test]
    fn subst_term_def() {
        let input = Parameterized {
            params: vec![
                Param::ty(Ident::new("A")),
                Param {
                    ident: Ident::new("f"),
                    content: Parameterized {
                        params: vec![
                            Param::ty(Ident::new("B")),
                            Param::term(Ident::new("b"), TypeExpr::var(-1)),
                        ],
                        inner: ParamContent::term(TypeExpr::var(-3)),
                    },
                },
                Param::ty(Ident::new("C")),
                Param::term(Ident::new("c"), TypeExpr::var(-1)),
                Param {
                    ident: Ident::new("d"),
                    content: Parameterized::new(ParamContent::Term {
                        ty: TypeExpr::var(-4),
                        def: Some(TermExpr::fun(
                            -3,
                            vec![Arg::ty(TypeExpr::var(-2)), Arg::term(TermExpr::var(-1))],
                        )),
                    }),
                },
            ],
            inner: TermExpr::fun(
                -4,
                vec![Arg::ty(TypeExpr::var(-5)), Arg::term(TermExpr::var(-1))],
            ),
        };
        let output = TermExpr::subst(
            CtxCow::Owned(input),
            CtxCow::Owned(vec![
                Arg::ty(TypeExpr::var(-42)),
                Arg {
                    value: Some(Parameterized {
                        params: vec![
                            Param::ty(Ident::new("B")),
                            Param::term(Ident::new("b"), TypeExpr::var(-1)),
                        ],
                        inner: ArgValue::Term(TermExpr::fun(
                            -25,
                            vec![Arg::term(TermExpr::var(-1))],
                        )),
                    }),
                },
                Arg::ty(TypeExpr::var(-35)),
                Arg::term(TermExpr::var(-51)),
                Arg::def(),
            ]),
        );
        assert_eq!(
            output.into_owned(),
            TermExpr::cast(
                TypeExpr::var(-42),
                TermExpr::fun(
                    -23,
                    vec![Arg::term(TermExpr::cast(
                        TypeExpr::var(-42),
                        TermExpr::cast(
                            TypeExpr::var(-42),
                            TermExpr::cast(
                                TypeExpr::var(-42),
                                TermExpr::fun(
                                    -23,
                                    vec![Arg::term(TermExpr::cast(
                                        TypeExpr::var(-35),
                                        TermExpr::cast(TypeExpr::var(-35), TermExpr::var(-51))
                                    ))]
                                )
                            )
                        )
                    ))]
                )
            )
        );
    }
}
