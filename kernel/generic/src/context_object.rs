use anyhow::Result;
use smallvec::SmallVec;

use crate::context::*;

pub const INLINE_PARAMS: usize = 8;

pub type InlineVec<T> = SmallVec<[T; INLINE_PARAMS]>;

pub const REF_CHUNK_LEN: usize = 16;

/// An object that lives in a specific context, so that variable indices are meaningful.
pub trait ContextObject: Clone {
    /// Low-level method that shifts variable indices between `start` (inclusive) `end` (exclusive)
    /// by `shift`, in a way that respects the distinction between globals and locals:
    /// * If `start` is < 0, i.e. we are shifting locals, then `start` and `end` are decreased upon
    ///   entering a binder, and `shift` is increased if `start + shift >= 0`, i.e. if we are
    ///   converting to globals.
    /// * Otherwise, `start` and `end` are not changed, but `shift` is decreased if
    ///   `start + shift < 0`, i.e. if we are converting to locals.
    ///
    /// Usually, we want to shift locals, so `start` and `end` are <= 0, and `start` indicates the
    /// number of loose bound variables we expect to exist. So if `start` is < 0, the method panics
    /// when it encounters a variable reference that is
    /// * below `start`, so not allowed to exist, or
    /// * between `end` and `end + shift` if `shift` is positive but `start + shift < 0`, which
    ///   means that the local variable is in the range we are "dropping".
    ///
    /// There are various use cases.
    /// * If `end` is 0 and `shift` is negative, we can regard this operation as making room for
    ///   `-shift` binders, which is exactly what we need during substitution when we place this
    ///   expression below some binders in the target expression.
    /// * The case that `end` is negative occurs during recursive calls, because when we enter a
    ///   subexpression under a binder, we need to ignore the local variables referring to that
    ///   binder. (E.g. when substituting, they are part of the copied/moved expression.)
    /// * `shift` may be positive in two cases: Either it is known that `shift` many bound variables
    ///   are unreferenced (e.g. in eta reduction, when the function must be shifted out of the
    ///   binder), or we are shifting variables from local to global when entering a binder.
    ///
    /// Do not use this method directly; use a higher-level method instead.
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex);

    /// Combination of `clone` and `shift_impl`. This may be optimized by specific implementations.
    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        let mut result = self.clone();
        result.shift_impl(start, end, shift);
        result
    }

    fn shift_to_subcontext<Ctx: Context>(&mut self, ctx: &Ctx, subctx: &Ctx) {
        self.shift_impl(ctx.locals_start(), 0, ctx.subcontext_shift(subctx));
    }

    fn shifted_to_subcontext<Ctx: Context>(&self, ctx: &Ctx, subctx: &Ctx) -> Self {
        self.shifted_impl(ctx.locals_start(), 0, ctx.subcontext_shift(subctx))
    }

    fn shift_to_supercontext<Ctx: Context>(&mut self, ctx: &Ctx, superctx: &Ctx) {
        let shift = superctx.subcontext_shift(ctx);
        self.shift_impl(ctx.locals_start(), shift, -shift);
    }

    fn shifted_to_supercontext<Ctx: Context>(&self, ctx: &Ctx, superctx: &Ctx) -> Option<Self> {
        if self.valid_in_superctx(ctx, superctx) {
            let shift = superctx.subcontext_shift(ctx);
            Some(self.shifted_impl(ctx.locals_start(), shift, -shift))
        } else {
            None
        }
    }

    fn shifted_from_var<Ctx: Context>(&self, subctx: &Ctx, var_idx_in_subctx: VarIndex) -> Self {
        if var_idx_in_subctx < 0 {
            self.shifted_impl(
                subctx.locals_start() - var_idx_in_subctx,
                0,
                var_idx_in_subctx,
            )
        } else {
            self.clone()
        }
    }

    /// For each variable in the range from `start` to `start + ref_counts.len()`, counts how often
    /// it is referenced, by increasing the corresponding item in `ref_counts`.
    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]);

    /// Similar to `count_refs_impl`, but just checks whether any references exist.
    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool;

    /// Checks if any of the topmost `len` local variables are referenced.
    fn valid_in_superctx<Ctx: Context>(&self, ctx: &Ctx, superctx: &Ctx) -> bool {
        !self.has_refs_impl(superctx.subcontext_shift(ctx), 0)
    }
}

impl<T: ContextObject> ContextObject for Box<T> {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        self.as_mut().shift_impl(start, end, shift)
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        Box::new(self.as_ref().shifted_impl(start, end, shift))
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        self.as_ref().count_refs_impl(start, ref_counts)
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        self.as_ref().has_refs_impl(start, end)
    }
}

impl<T: ContextObject> ContextObject for Option<T> {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        if let Some(s) = self {
            s.shift_impl(start, end, shift);
        }
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        if let Some(s) = self {
            Some(s.shifted_impl(start, end, shift))
        } else {
            None
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        if let Some(s) = self {
            s.count_refs_impl(start, ref_counts);
        }
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        if let Some(s) = self {
            s.has_refs_impl(start, end)
        } else {
            false
        }
    }
}

/// A `ContextObject` that supports some form of substitution: Each variable reference may be
/// substituted with a value of type `SubstArg`.
///
/// In the simplest case, where a variable reference is just an expression containing a single
/// `VarIndex`, `SubstArg` can just be the expression type. However, in cases where variable
/// references are more complex, `SubstArg` needs to hold whatever data is necessary to completely
/// replace a variable reference.
pub trait ContextObjectWithSubst<SubstArg>: ContextObject {
    /// Substitutes the variables in the range from `args_start` to `args_start + args.len()` with
    /// `args` (more precisely, with data provided by `args`), adjusting indices in arguments as
    /// required. Indices between `shift_start` and `args_start` are shifted up by `args.len()`, and
    /// if `shift_start` < 0, indices smaller than `shift_start` must not exist, as in `shift_impl`.
    ///
    /// `ref_counts` should either be empty or have the same length as `args`. In the latter case,
    /// it should be the result of the corresponding call to `count_refs_impl`. This reduces memory
    /// allocations by calling `std::mem::take` on each item in `args` when its reference count
    /// reaches 1. Otherwise, the method does not modify `args`.
    ///
    /// If the arguments have loose bound variables, they are considered to live in the target
    /// context of the substitution, i.e. their local indices are shifted up by
    /// `args_start + args.len()`, and the limit of their loose bound variables is given by
    /// `shift_start - args_start`.
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        ref_counts: &mut [usize],
    );

    fn substitute_int(
        &mut self,
        mut shift_start: VarIndex,
        mut args_start: VarIndex,
        mut args: &mut [SubstArg],
        may_take_args: bool,
    ) {
        if may_take_args {
            // Since we can only allocate a fixed amount of space on the stack, we split the
            // substitution into chunks of `REF_CHUNK_LEN` or less.
            // The order in which we iterate over chunks is important. If we did it in reverse, we
            // would need to take index shifts into account. However, this does not work because the
            // `args_start` argument of `substitute_impl` also influences how indices in arguments
            // are adjusted.
            let mut ref_counts = [0; REF_CHUNK_LEN];
            let mut len = args.len();
            while len > REF_CHUNK_LEN {
                self.count_refs_impl(args_start, &mut ref_counts);
                let (cur_args, rest_args) = args.split_at_mut(REF_CHUNK_LEN);
                self.substitute_impl(shift_start, args_start, cur_args, &mut ref_counts);
                debug_assert_eq!(ref_counts, [0; REF_CHUNK_LEN]);
                len -= REF_CHUNK_LEN;
                shift_start += REF_CHUNK_LEN as VarIndex;
                args_start += REF_CHUNK_LEN as VarIndex;
                args = rest_args;
            }
            let rest_ref_counts = &mut ref_counts[..len];
            self.count_refs_impl(args_start, rest_ref_counts);
            self.substitute_impl(shift_start, args_start, args, rest_ref_counts);
            debug_assert_eq!(ref_counts, [0; REF_CHUNK_LEN]);
        } else {
            self.substitute_impl(shift_start, args_start, args, &mut []);
        }
    }

    /// Substitutes the topmost `args.len()` local variables with `args` (more precisely, with data
    /// provided by `args`), adjusting indices in arguments as required, and shifting indices in the
    /// result up by `args.len()`. The expression is assumed to live in a subcontext of `subst_ctx`
    /// with `args.len()` additional variables.
    ///
    /// `may_take_args` may be set to avoid unnecessary memory allocations in case `args` is no
    /// longer needed afterwards.
    ///
    /// If the arguments have loose bound variables, they are considered to live in the target
    /// context of the substitution.
    fn substitute<Ctx: Context>(
        &mut self,
        args: &mut [SubstArg],
        may_take_args: bool,
        subst_ctx: &Ctx,
    ) {
        let args_start = -(args.len() as VarIndex);
        let shift_start = subst_ctx.locals_start() + args_start;

        self.substitute_int(shift_start, args_start, args, may_take_args);
    }
}

impl<SubstArg, T: ContextObjectWithSubst<SubstArg>> ContextObjectWithSubst<SubstArg> for Box<T> {
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        ref_counts: &mut [usize],
    ) {
        self.as_mut()
            .substitute_impl(shift_start, args_start, args, ref_counts)
    }
}

impl<SubstArg, T: ContextObjectWithSubst<SubstArg>> ContextObjectWithSubst<SubstArg> for Option<T> {
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        ref_counts: &mut [usize],
    ) {
        if let Some(s) = self {
            s.substitute_impl(shift_start, args_start, args, ref_counts);
        }
    }
}

pub trait ContextObjectWithCmp<Ctx: Context>: ContextObject {
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool>;

    /// Checks whether the expression matches `target` when shifted to the subcontext
    /// `target_subctx`.
    fn shift_and_compare(&self, ctx: &Ctx, target: &Self, target_subctx: &Ctx) -> Result<bool> {
        debug_assert!(ctx.subcontext_shift(target_subctx) <= 0);
        self.shift_and_compare_impl(ctx, ctx, target, target_subctx)
    }

    /// Checks whether the expression matches `target`.
    fn compare(&self, target: &Self, ctx: &Ctx) -> Result<bool> {
        self.shift_and_compare(ctx, target, ctx)
    }
}

impl<Ctx: Context, T: ContextObjectWithCmp<Ctx>> ContextObjectWithCmp<Ctx> for Box<T> {
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        self.as_ref()
            .shift_and_compare_impl(ctx, orig_ctx, target, target_subctx)
    }
}

impl<Ctx: Context, T: ContextObjectWithCmp<Ctx>> ContextObjectWithCmp<Ctx> for Option<T> {
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        match (self, target) {
            (Some(s), Some(t)) => s.shift_and_compare_impl(ctx, orig_ctx, t, target_subctx),
            (None, None) => Ok(true),
            (_, _) => Ok(false),
        }
    }
}

pub trait CanBeEmpty {
    fn is_empty(&self) -> bool;
}

pub trait ContextObjectWithSubstCmp<SubstArg: CanBeEmpty, Ctx: Context>:
    ContextObjectWithSubst<SubstArg> + ContextObjectWithCmp<Ctx>
{
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool>;

    fn substitute_and_shift_and_compare(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        debug_assert_eq!(subst_ctx.subcontext_shift(ctx), -(args.len() as VarIndex));
        debug_assert!(subst_ctx.subcontext_shift(target_subctx) <= 0);
        self.substitute_and_shift_and_compare_impl(ctx, args, subst_ctx, target, target_subctx)
    }

    /// Performs substitution like `substitute`, but compares the result against `target` instead of
    /// mutating. `SubstArg::default()` indicates missing arguments. Whenever such an argument is
    /// encountered during comparison, it is filled with the corresponding part of `target`.
    fn substitute_and_compare(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        target: &Self,
        subst_ctx: &Ctx,
    ) -> Result<bool> {
        self.substitute_and_shift_and_compare(ctx, args, subst_ctx, target, subst_ctx)
    }
}

impl<SubstArg: CanBeEmpty, Ctx: Context, T: ContextObjectWithSubstCmp<SubstArg, Ctx>>
    ContextObjectWithSubstCmp<SubstArg, Ctx> for Box<T>
{
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        self.as_ref().substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            target,
            target_subctx,
        )
    }
}

impl<SubstArg: CanBeEmpty, Ctx: Context, T: ContextObjectWithSubstCmp<SubstArg, Ctx>>
    ContextObjectWithSubstCmp<SubstArg, Ctx> for Option<T>
{
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        match (self, target) {
            (Some(s), Some(t)) => {
                s.substitute_and_shift_and_compare_impl(ctx, args, subst_ctx, t, target_subctx)
            }
            (None, None) => Ok(true),
            (_, _) => Ok(false),
        }
    }
}

#[macro_export]
macro_rules! primitive_context_object {
    ($Ty:ty) => {
        impl ContextObject for $Ty {
            fn shift_impl(&mut self, _: VarIndex, _: VarIndex, _: VarIndex) {}

            fn count_refs_impl(&self, _: VarIndex, _: &mut [usize]) {}

            fn has_refs_impl(&self, _: VarIndex, _: VarIndex) -> bool {
                false
            }
        }

        impl<SubstArg> ContextObjectWithSubst<SubstArg> for $Ty {
            fn substitute_impl(
                &mut self,
                _: VarIndex,
                _: VarIndex,
                _: &mut [SubstArg],
                _: &mut [usize],
            ) {
            }
        }

        impl<Ctx: Context> ContextObjectWithCmp<Ctx> for $Ty {
            fn shift_and_compare_impl(
                &self,
                _: &Ctx,
                _: &Ctx,
                _: &Self,
                _: &Ctx,
            ) -> anyhow::Result<bool> {
                Ok(true)
            }
        }

        impl<SubstArg: CanBeEmpty, Ctx: Context> ContextObjectWithSubstCmp<SubstArg, Ctx> for $Ty {
            fn substitute_and_shift_and_compare_impl(
                &self,
                _: &Ctx,
                _: &mut [SubstArg],
                _: &Ctx,
                _: &Self,
                _: &Ctx,
            ) -> anyhow::Result<bool> {
                Ok(true)
            }
        }
    };
}

primitive_context_object!(());
primitive_context_object!(bool);
primitive_context_object!(usize);

#[macro_export]
macro_rules! iterable_context_object {
    ($Ty:ident) => {
        impl<T: ContextObject> ContextObject for $Ty<T> {
            fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
                self.iter_mut()
                    .for_each(|item| item.shift_impl(start, end, shift))
            }

            fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
                self.iter()
                    .map(|item| item.shifted_impl(start, end, shift))
                    .collect()
            }

            fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
                self.iter()
                    .for_each(|item| item.count_refs_impl(start, ref_counts))
            }

            fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
                self.iter().any(|item| item.has_refs_impl(start, end))
            }
        }

        impl<SubstArg, T: ContextObjectWithSubst<SubstArg>> ContextObjectWithSubst<SubstArg>
            for $Ty<T>
        {
            fn substitute_impl(
                &mut self,
                shift_start: VarIndex,
                args_start: VarIndex,
                args: &mut [SubstArg],
                ref_counts: &mut [usize],
            ) {
                self.iter_mut().for_each(|item| {
                    item.substitute_impl(shift_start, args_start, args, ref_counts)
                })
            }
        }

        impl<Ctx: Context, T: ContextObjectWithCmp<Ctx>> ContextObjectWithCmp<Ctx> for $Ty<T> {
            fn shift_and_compare_impl(
                &self,
                ctx: &Ctx,
                orig_ctx: &Ctx,
                target: &Self,
                target_subctx: &Ctx,
            ) -> Result<bool> {
                if self.len() != target.len() {
                    return Ok(false);
                }
                for (item, target_item) in self.iter().zip(target.iter()) {
                    if !item.shift_and_compare_impl(ctx, orig_ctx, target_item, target_subctx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }

        impl<SubstArg: CanBeEmpty, Ctx: Context, T: ContextObjectWithSubstCmp<SubstArg, Ctx>>
            ContextObjectWithSubstCmp<SubstArg, Ctx> for $Ty<T>
        {
            fn substitute_and_shift_and_compare_impl(
                &self,
                ctx: &Ctx,
                args: &mut [SubstArg],
                subst_ctx: &Ctx,
                target: &Self,
                target_subctx: &Ctx,
            ) -> Result<bool> {
                if self.len() != target.len() {
                    return Ok(false);
                }
                for (item, target_item) in self.iter().zip(target.iter()) {
                    if !item.substitute_and_shift_and_compare_impl(
                        ctx,
                        args,
                        subst_ctx,
                        target_item,
                        target_subctx,
                    )? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    };
}

iterable_context_object!(Vec);
iterable_context_object!(InlineVec);

pub trait SubstInto<SubstArg, SubstResult> {
    fn get_subst_arg_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        ref_counts: &mut [usize],
    ) -> Option<SubstResult>;
}

pub trait SubstCmpInto<SubstArg: CanBeEmpty, SubstResult, Ctx: Context> {
    fn compare_subst_arg_impl(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &SubstResult,
        target_subctx: &Ctx,
    ) -> Option<Result<bool>>;
}
