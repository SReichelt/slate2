use std::borrow::Cow;

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
                                offset: (-idx) as usize,
                            });
                        }
                    }
                    cur_ctx = parent;
                }
                Context::Quoted { orig } => {
                    if cur_idx < 0 {
                        let mut param = orig.param(cur_idx);
                        param.weaken((-idx) as usize);
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
                    offset: param.offset,
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
    pub offset: CtxOffset,
}

impl<'a, T: ?Sized> CtxRef<'a, T> {
    pub fn new(value: &'a T) -> Self {
        CtxRef { value, offset: 0 }
    }

    pub fn to_owned(&self) -> T
    where
        T: ContextObject,
    {
        self.value.weakened(self.offset)
    }

    // Obtains a context-dependent reference to a member.
    // Warning: projecting across a parameterization is illegal, as references to the parameters
    // must be excluded from the adjustment.
    pub fn project<R>(&self, f: impl FnOnce(&'a T) -> &'a R) -> CtxRef<'a, R> {
        CtxRef {
            value: f(&self.value),
            offset: self.offset,
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
pub enum CtxCow<'a, T: ?Sized> {
    Borrowed(CtxRef<'a, T>),
    // TODO: Not sure if boxing here is a good idea; should measure performance and memory usage.
    Owned(Box<T>),
}

impl<'a, T: ?Sized> CtxCow<'a, T> {
    pub fn new(value: Cow<'a, T>) -> Self
    where
        T: Sized + Clone,
    {
        match value {
            Cow::Borrowed(value) => Self::borrowed(value),
            Cow::Owned(value) => Self::owned(value),
        }
    }

    pub fn borrowed(value: &'a T) -> Self {
        CtxCow::Borrowed(CtxRef::new(value))
    }

    pub fn owned(value: T) -> Self
    where
        T: Sized,
    {
        CtxCow::Owned(Box::new(value))
    }

    pub fn as_ref(&'a self) -> CtxRef<'a, T> {
        match self {
            CtxCow::Borrowed(ctx_ref) => *ctx_ref,
            CtxCow::Owned(value) => CtxRef::new(value),
        }
    }

    pub fn into_owned(self) -> T
    where
        T: ContextObject,
    {
        match self {
            CtxCow::Borrowed(ctx_ref) => ctx_ref.to_owned(),
            CtxCow::Owned(value) => *value,
        }
    }

    pub fn weaken(&mut self, offset: usize)
    where
        T: ContextObject,
    {
        match self {
            CtxCow::Borrowed(ctx_ref) => ctx_ref.offset += offset,
            CtxCow::Owned(value) => value.weaken(offset),
        }
    }

    // Obtains a context-dependent reference to a member.
    // Warning: projecting across a parameterization is illegal, as references to the parameters
    // must be excluded from the adjustment.
    pub fn project<R: Clone>(self, f: impl FnOnce(Cow<'a, T>) -> Cow<'a, R>) -> CtxCow<'a, R>
    where
        T: Clone,
    {
        match self {
            CtxCow::Borrowed(ctx_ref) => CtxCow::Borrowed(ctx_ref.project(|value| {
                let Cow::Borrowed(projected) = f(Cow::Borrowed(value)) else {
                    panic!("projecting from borrowed to owned is not allowed")
                };
                projected
            })),
            CtxCow::Owned(value) => CtxCow::new(f(Cow::Owned(*value))),
        }
    }
}

pub trait ContextObject: Sized + Clone {
    fn weaken(&mut self, offset: usize);

    fn weakened(&self, offset: usize) -> Self {
        let mut clone = self.clone();
        if offset != 0 {
            clone.weaken(offset);
        }
        clone
    }

    // Warning: The argument to `project` is always `src.data`, ignoring any context offset in
    // `src`. Therefore, if `project` depends on a context, make sure that `src` does not have any
    // offset (as ensured by `map_subst_ctx`).
    fn map_subst<'a, Src: ToOwned>(
        src: CtxCow<'a, Parameterized<Src>>,
        project: impl FnOnce(Cow<'a, Src>) -> CtxCow<'a, Self>,
        args: CtxCow<'a, [Arg]>,
    ) -> CtxCow<'a, Self>;

    fn subst<'a>(
        value: CtxCow<'a, Parameterized<Self>>,
        args: CtxCow<'a, [Arg]>,
    ) -> CtxCow<'a, Self> {
        Self::map_subst(value, CtxCow::new, args)
    }

    fn map_subst_ctx<'a, Src: Clone>(
        src: &'a Parameterized<Src>,
        project: impl FnOnce(&'a Src, &Context<'a>) -> CtxCow<'a, Self>,
        args: CtxCow<'a, [Arg]>,
        ctx: &'a Context<'a>,
    ) -> CtxCow<'a, Self> {
        Self::map_subst(
            CtxCow::borrowed(src),
            |_| ctx.with_parameterization(src, project),
            args,
        )
    }
}
