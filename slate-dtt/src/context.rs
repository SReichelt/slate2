use std::{
    borrow::{Borrow, BorrowMut, Cow},
    convert::identity,
};

use slate_lang_def::parser::layer3_parameter_identifier::ParamIdx;

use crate::{expr::*, meta::MetaGlobals};

pub enum Context<'a> {
    Root {
        globals: &'a [Param],
        meta_globals: &'a MetaGlobals,
    },
    Frame {
        parent: &'a Context<'a>,
        params: &'a [Param],
    },
    Quoted {
        orig: &'a Context<'a>,
    },
}

impl<'a> Context<'a> {
    pub fn new(globals: &'a [Param], meta_globals: &'a MetaGlobals) -> Self {
        Context::Root {
            globals,
            meta_globals,
        }
    }

    pub fn param(&self, idx: ParamIdx) -> CtxCow<'a, Param> {
        let mut cur_ctx = self;
        let mut cur_idx = idx;
        loop {
            match cur_ctx {
                Context::Root { globals, .. } => {
                    assert!(cur_idx >= 0);
                    return CtxCow::borrowed(&globals[cur_idx as usize]);
                }
                Context::Frame { parent, params } => {
                    if cur_idx < 0 {
                        cur_idx += params.len() as isize;
                        if cur_idx >= 0 {
                            return CtxCow::Borrowed(CtxRef {
                                value: &params[cur_idx as usize],
                                weaken_by: (-idx) as CtxOffset,
                            });
                        }
                    }
                    cur_ctx = parent;
                }
                Context::Quoted { orig } => {
                    if cur_idx < 0 {
                        let mut param = orig.param(cur_idx);
                        param.weaken((-idx) as CtxOffset);
                        return self.unquote_param(param.as_ref());
                    }
                    cur_ctx = orig;
                }
            }
        }
    }

    pub fn extended<'b>(&'b self, params: &'b [Param]) -> Context<'b> {
        Context::Frame {
            parent: self,
            params,
        }
    }

    pub fn quoted<'b>(&'b self) -> Context<'b> {
        Context::Quoted { orig: self }
    }

    pub fn with_parameterization<'b, T, R>(
        &'b self,
        obj: &'b Parameterized<T>,
        f: impl FnOnce(&'b T, &Context<'b>) -> R,
    ) -> R {
        let new_ctx = self.extended(&obj.params);
        f(&obj.inner, &new_ctx)
    }

    pub fn meta_globals(&self) -> &MetaGlobals {
        let mut cur_ctx = self;
        loop {
            match cur_ctx {
                Context::Root { meta_globals, .. } => return meta_globals,
                Context::Frame { parent, .. } => cur_ctx = parent,
                Context::Quoted { orig } => cur_ctx = orig,
            }
        }
    }

    // TODO: We need to present meta-level functions as parameterizations, as that is what the
    // quotation mechanism outputs.

    fn unquote_param(&self, param: CtxRef<Param>) -> CtxCow<'a, Param> {
        // For the moment, a variable can only be used as an antiquotation if its type is
        // directly `Type` or `A.Inst` where `A` is a variable or a quoted type.
        if let ParamContent::Term {
            ty: TypeExpr::Base(BaseExpr::Var(var_expr)),
            ..
        } = &param.value.content.inner
        {
            let meta_globals = self.meta_globals();
            if var_expr.idx == meta_globals.type_ty_idx {
                return CtxCow::owned(self.create_unquoted_param(param, ParamContent::ty()));
            } else if var_expr.idx == meta_globals.inst_ty_idx {
                let ParamContent::Term {
                    ty: TypeExpr::Base(BaseExpr::Var(var_expr)),
                    ..
                } = param.to_owned().content.inner
                else {
                    unreachable!()
                };
                let ArgValue::Term(ty_expr) = var_expr
                    .args
                    .into_iter()
                    .next()
                    .unwrap()
                    .value
                    .unwrap()
                    .inner
                else {
                    unreachable!()
                };
                return CtxCow::owned(
                    self.create_unquoted_param(
                        param,
                        ParamContent::term(self.unquote_type(ty_expr)),
                    ),
                );
            }
        }
        static DUMMY_PARAM: Param = Param {
            ident: Ident::none(),
            content: Parameterized::new(ParamContent::term(TypeExpr::Base(BaseExpr::Placeholder))),
        };
        CtxCow::borrowed(&DUMMY_PARAM)
    }

    fn create_unquoted_param(&self, param: CtxRef<Param>, content: ParamContent) -> Param {
        let params = param
            .value
            .content
            .params
            .iter()
            .map(|p| {
                self.unquote_param(CtxRef {
                    value: p,
                    weaken_by: param.weaken_by,
                })
                .into_owned()
            })
            .collect();
        Param {
            ident: param.value.ident.clone(),
            content: Parameterized {
                params,
                inner: content,
            },
        }
    }

    fn unquote_type(&self, ty_expr: TermExpr) -> TypeExpr {
        match ty_expr {
            TermExpr::Base(BaseExpr::Var(ty_var_expr)) => {
                // We can support both globals and locals here. They behave very differently but
                // hopefully both correctly.
                if ty_var_expr.args.is_empty() {
                    TypeExpr::Base(BaseExpr::Var(ty_var_expr))
                } else {
                    // TODO: need to unquote the arguments as well
                    todo!()
                }
            }
            TermExpr::QuotedType(ty) => *ty,
            _ => TypeExpr::Base(BaseExpr::Placeholder),
        }
    }
}

pub type CtxOffset = usize;

// A reference to a context-dependent object, potentially weakened by a context offset. (This lets
// us delay the actual weakening operation, often avoiding the construction of a new object.)
pub struct CtxRef<'a, T: ?Sized> {
    pub value: &'a T,
    pub weaken_by: CtxOffset,
}

impl<'a, T: ?Sized> CtxRef<'a, T> {
    pub fn new(value: &'a T) -> Self {
        CtxRef {
            value,
            weaken_by: 0,
        }
    }

    pub fn to_owned(&self) -> T::Owned
    where
        T: ContextObject,
    {
        self.value.weakened(0, self.weaken_by)
    }

    pub fn weaken(&mut self, weaken_by: CtxOffset) {
        self.weaken_by += weaken_by;
    }

    // Obtains a context-dependent reference to a member.
    // Warning: projecting across a parameterization is illegal, as references to the parameters
    // must be excluded from the adjustment.
    pub fn project<R: ?Sized>(&self, f: impl FnOnce(&'a T) -> &'a R) -> CtxRef<'a, R> {
        CtxRef {
            value: f(&self.value),
            weaken_by: self.weaken_by,
        }
    }
}

impl<'a, T: ?Sized> Copy for CtxRef<'a, T> {}

impl<'a, T: ?Sized> Clone for CtxRef<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

#[derive(Clone)]
pub enum CtxCow<'a, T: ?Sized + ToOwned> {
    Borrowed(CtxRef<'a, T>),
    Owned(T::Owned),
}

impl<'a, T: ?Sized + ToOwned> CtxCow<'a, T> {
    pub fn new(value: Cow<'a, T>) -> Self {
        match value {
            Cow::Borrowed(value) => Self::borrowed(value),
            Cow::Owned(value) => Self::owned(value),
        }
    }

    pub fn borrowed(value: &'a T) -> Self {
        CtxCow::Borrowed(CtxRef::new(value))
    }

    pub fn owned(value: T::Owned) -> Self {
        CtxCow::Owned(value)
    }

    pub fn as_ref(&'a self) -> CtxRef<'a, T> {
        match self {
            CtxCow::Borrowed(ctx_ref) => *ctx_ref,
            CtxCow::Owned(value) => CtxRef::new(value.borrow()),
        }
    }

    pub fn as_borrowed(&'a self) -> Self {
        CtxCow::Borrowed(self.as_ref())
    }

    // Intentionally not exported because it ignores `weaken_by`.
    fn value(&'a self) -> &'a T {
        match self {
            CtxCow::Borrowed(ctx_ref) => ctx_ref.value,
            CtxCow::Owned(value) => value.borrow(),
        }
    }

    pub fn into_owned(self) -> T::Owned
    where
        T: ContextObject,
    {
        match self {
            CtxCow::Borrowed(ctx_ref) => ctx_ref.to_owned(),
            CtxCow::Owned(value) => value,
        }
    }

    pub fn weaken(&mut self, weaken_by: CtxOffset)
    where
        T: ContextObject,
    {
        match self {
            CtxCow::Borrowed(ctx_ref) => ctx_ref.weaken(weaken_by),
            CtxCow::Owned(value) => value.borrow_mut().weaken(0, weaken_by),
        }
    }

    pub fn weakened(&self, weaken_by: CtxOffset) -> T::Owned
    where
        T: ContextObject,
    {
        let mut ctx_ref = self.as_ref();
        ctx_ref.weaken(weaken_by);
        ctx_ref.to_owned()
    }

    /// Obtains a context-dependent reference to a member.
    /// Warning: projecting across a parameterization is illegal, as references to the parameters
    /// must be excluded from the adjustment.
    pub fn project<R: ?Sized + ToOwned>(
        self,
        f: impl FnOnce(Cow<'a, T>) -> Cow<'a, R>,
    ) -> CtxCow<'a, R> {
        match self {
            CtxCow::Borrowed(ctx_ref) => CtxCow::Borrowed(ctx_ref.project(|value| {
                let Cow::Borrowed(projected) = f(Cow::Borrowed(value)) else {
                    panic!("projecting from borrowed to owned is not allowed")
                };
                projected
            })),
            CtxCow::Owned(value) => CtxCow::new(f(Cow::Owned(value))),
        }
    }
}

impl<'a, T> CtxCow<'a, [T]>
where
    [T]: ToOwned<Owned = Vec<T>>,
{
    pub fn len(&self) -> usize {
        self.value().len()
    }

    /// Note: Do not use for parameter lists; the context offset of the selected param would be
    /// incorrect.
    pub fn project_idx(self, idx: usize) -> (Self, CtxCow<'a, T>)
    where
        T: Clone,
    {
        match self {
            CtxCow::Borrowed(ctx_ref) => (
                CtxCow::Borrowed(CtxRef {
                    value: &ctx_ref.value[..idx],
                    weaken_by: ctx_ref.weaken_by,
                }),
                CtxCow::Borrowed(CtxRef {
                    value: &ctx_ref.value[idx],
                    weaken_by: ctx_ref.weaken_by,
                }),
            ),
            CtxCow::Owned(mut value) => {
                value.truncate(idx + 1);
                let item = value.pop().unwrap();
                (CtxCow::Owned(value), CtxCow::Owned(item))
            }
        }
    }
}

impl<'a, T: Clone> CtxCow<'a, Option<T>> {
    pub fn as_option(self) -> Option<CtxCow<'a, T>> {
        match self {
            CtxCow::Borrowed(ctx_ref) => ctx_ref.value.as_ref().map(|value| {
                CtxCow::Borrowed(CtxRef {
                    value,
                    weaken_by: ctx_ref.weaken_by,
                })
            }),
            CtxCow::Owned(value) => value.map(CtxCow::Owned),
        }
    }
}

pub trait ContextObject: ToOwned<Owned: BorrowMut<Self>> {
    /// Adjust references to local variables < `-offset` to be correct in a subcontext with
    /// `weaken_by` additional variables.
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset);

    /// Equivalent to `to_owned` followed by `weaken`, but can be specialized to improve
    /// performance.
    /// Note: Rather than calling this method directly, consider creating a `CtxRef` so that cloning
    /// only happens later if needed.
    #[must_use]
    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self::Owned {
        let mut clone = self.to_owned();
        if weaken_by != 0 {
            clone.borrow_mut().weaken(offset, weaken_by);
        }
        clone
    }

    #[must_use]
    fn subst<'a>(
        value: CtxCow<'a, Parameterized<Self>>,
        args: CtxCow<'_, [Arg]>,
    ) -> CtxCow<'a, Self>
    where
        Self: Clone,
    {
        Self::map_subst(value, identity, args)
    }

    #[must_use]
    fn map_subst<'a, Src: Clone>(
        src: CtxCow<'a, Parameterized<Src>>,
        project: impl FnOnce(Cow<'a, Src>) -> Cow<'a, Self>,
        args: CtxCow<'_, [Arg]>,
    ) -> CtxCow<'a, Self> {
        let params_len = src.value().params.len();
        debug_assert_eq!(args.len(), params_len);
        if params_len > 0 {
            let (mut inner, params) = match src {
                CtxCow::Borrowed(ctx_ref) => {
                    let projected = project(Cow::Borrowed(&ctx_ref.value.inner));
                    (
                        projected.weakened(params_len, ctx_ref.weaken_by),
                        CtxCow::Borrowed(CtxRef {
                            value: ctx_ref.value.params.as_slice(),
                            weaken_by: ctx_ref.weaken_by,
                        }),
                    )
                }
                CtxCow::Owned(value) => {
                    let projected = project(Cow::Owned(value.inner));
                    (projected.into_owned(), CtxCow::Owned(value.params))
                }
            };
            inner.borrow_mut().subst_impl(0, params, args);
            CtxCow::Owned(inner)
        } else {
            src.project(|value| match value {
                Cow::Borrowed(value) => project(Cow::Borrowed(&value.inner)),
                Cow::Owned(value) => project(Cow::Owned(value.inner)),
            })
        }
    }

    /// Replaces references to any param in `params` with the corresponding arg in `args`,
    /// specifically:
    /// * All locals >= `-offset` are untouched.
    /// * Locals < `-offset` and >= `-(offset + params.len())` are replaced with the corresponding
    ///   arguments weakened by `offset`, taking into account definition params and inserting casts
    ///   as necessary. `params` is assumed to live in the context that is offset by both `offset`
    ///   and `params.len()`.
    /// * Locals < `-(offset + params.len())` are increased by `params`.
    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    );
}

impl ContextObject for () {
    fn weaken(&mut self, _offset: CtxOffset, _weaken_by: CtxOffset) {}

    fn subst_impl(
        &mut self,
        _offset: CtxOffset,
        _params: CtxCow<'_, [Param]>,
        _args: CtxCow<'_, [Arg]>,
    ) {
    }
}

impl<T: ContextObject<Owned = T> + Clone> ContextObject for Option<T> {
    fn weaken(&mut self, offset: CtxOffset, weaken_by: CtxOffset) {
        if let Some(value) = self {
            value.weaken(offset, weaken_by);
        }
    }

    fn weakened(&self, offset: CtxOffset, weaken_by: CtxOffset) -> Self::Owned {
        self.as_ref().map(|value| value.weakened(offset, weaken_by))
    }

    fn subst_impl(
        &mut self,
        offset: CtxOffset,
        params: CtxCow<'_, [Param]>,
        args: CtxCow<'_, [Arg]>,
    ) {
        if let Some(value) = self {
            value.subst_impl(offset, params, args);
        }
    }
}
