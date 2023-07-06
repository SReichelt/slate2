use std::{
    fmt::{self, Debug},
    mem::take,
};

use anyhow::Result;

use crate::{context::*, context_object::*};

/// A simple variable reference. This is the prototypical context object, but obviously does not
/// support substitution by itself.
#[derive(Clone, PartialEq)]
pub struct Var(pub VarIndex);

impl Default for Var {
    fn default() -> Self {
        Var(VarIndex::MAX)
    }
}

impl Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Var(idx) = *self;
        write!(f, "#{idx}")
    }
}

impl ContextObject for Var {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        let Var(idx) = self;
        if *idx < start {
            if start < 0 {
                panic!("unexpected loose bound variable with index {idx} (start: {start})");
            }
        } else if *idx < end {
            *idx += shift;
        } else if *idx < end + shift && start + shift < 0
        // implies shift > 0 and start < 0
        {
            panic!("attempted to drop referenced bound variable with index {idx}");
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        let Var(idx) = *self;
        if idx >= start {
            let end = start + ref_counts.len() as VarIndex;
            if idx < end {
                let array_idx = (idx - start) as usize;
                ref_counts[array_idx] += 1;
            }
        }
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        let Var(idx) = *self;
        idx >= start && idx < end
    }
}

impl<Ctx: Context> ContextObjectWithCmp<Ctx> for Var {
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        let Var(mut idx) = *self;
        let locals_start = ctx.locals_start();
        if idx < locals_start {
            panic!("unexpected loose bound variable with index {idx} (start: {locals_start})");
        } else if ctx.is_local_in_supercontext(idx, orig_ctx) {
            let shift = target_subctx.locals_start() - locals_start;
            idx += shift;
        } else {
            // This corresponds to the panic in shift_impl. It should be impossible to trigger if
            // target_subctx is a subcontext of orig_ctx, as we never shift up then.
            debug_assert!(!target_subctx.is_local_in_supercontext(idx, orig_ctx));
        }
        let Var(target_idx) = *target;
        Ok(idx == target_idx)
    }
}

impl<SubstArg: ContextObject + Default> SubstInto<SubstArg, SubstArg> for Var {
    fn get_subst_arg_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        ref_counts: &mut [usize],
    ) -> Option<SubstArg> {
        let Var(idx) = *self;
        if idx < shift_start {
            if shift_start < 0 {
                panic!("unexpected loose bound variable with index {idx} (start: {shift_start})");
            }
        } else if idx >= args_start {
            let args_end = args_start + (args.len() as VarIndex);
            if idx < args_end {
                let array_idx = (idx - args_start) as usize;
                let arg = &mut args[array_idx];
                if array_idx < ref_counts.len() {
                    let ref_count = &mut ref_counts[array_idx];
                    *ref_count -= 1;
                    if *ref_count == 0 {
                        if shift_start < 0 {
                            arg.shift_impl(shift_start - args_start, 0, args_end);
                        }
                        return Some(take(arg));
                    }
                }
                if shift_start < 0 {
                    return Some(arg.shifted_impl(shift_start - args_start, 0, args_end));
                } else {
                    return Some(arg.clone());
                }
            }
        }
        None
    }
}

impl<Ctx: Context, SubstArg: ContextObjectWithCmp<Ctx> + Default + CanBeEmpty>
    SubstCmpInto<SubstArg, SubstArg, Ctx> for Var
{
    fn compare_subst_arg_impl(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &SubstArg,
        target_subctx: &Ctx,
    ) -> Option<Result<bool>> {
        let Var(idx) = *self;
        let locals_start = ctx.locals_start();
        if idx < locals_start {
            panic!("unexpected loose bound variable with index {idx} (start: {locals_start})");
        } else if !ctx.is_local_in_supercontext(idx, subst_ctx) {
            let args_start = subst_ctx.subcontext_shift(ctx);
            debug_assert!(idx >= args_start);
            let args_end = args_start + (args.len() as VarIndex);
            if idx < args_end {
                let array_idx = (idx - args_start) as usize;
                let arg = &mut args[array_idx];
                if arg.is_empty() {
                    let arg_shift = subst_ctx.subcontext_shift(target_subctx);
                    if target.has_refs_impl(arg_shift, 0) {
                        return Some(Ok(false));
                    }
                    *arg = target.shifted_impl(target_subctx.locals_start(), arg_shift, -arg_shift);
                    return Some(Ok(true));
                }
                return Some(arg.shift_and_compare(subst_ctx, target, target_subctx));
            }
        }
        None
    }
}

fn enter_binder_for_shift<const PARAM_LEN: VarIndex>(
    start: &mut VarIndex,
    end: &mut VarIndex,
    shift: &mut VarIndex,
) {
    if PARAM_LEN != 0 {
        if *start < 0 {
            // Shifting locals.
            if *start + *shift >= 0 {
                // Converting to globals.
                *shift += PARAM_LEN;
            }
            *start -= PARAM_LEN;
            *end -= PARAM_LEN;
        } else {
            // Shifting globals.
            if *start + *shift < 0 {
                // Converting to locals.
                *shift -= PARAM_LEN;
            }
        }
    }
}

fn enter_binder_for_start_and_end<const PARAM_LEN: VarIndex>(
    start: &mut VarIndex,
    end: &mut VarIndex,
) {
    if PARAM_LEN != 0 {
        if *start < 0 {
            // Shifting locals.
            *start -= PARAM_LEN;
            *end -= PARAM_LEN;
        }
    }
}

fn enter_binder_for_start<const PARAM_LEN: VarIndex>(start: &mut VarIndex) {
    if PARAM_LEN != 0 {
        if *start < 0 {
            // Shifting locals.
            *start -= PARAM_LEN;
        }
    }
}

/// A generic abstraction over `Lambda` and `App`. If `PARAM_LEN` is nonzero, indices in the body
/// are offset by that amount, formalizing the notion that the body depends on the parameter.
#[derive(Clone, PartialEq, Default)]
pub struct ParameterizedObject<Param, Body, const PARAM_LEN: VarIndex> {
    pub param: Param,
    pub body: Body,
}

impl<Param: ContextObject, Body: ContextObject, const PARAM_LEN: VarIndex> ContextObject
    for ParameterizedObject<Param, Body, PARAM_LEN>
{
    fn shift_impl(&mut self, mut start: VarIndex, mut end: VarIndex, mut shift: VarIndex) {
        if shift == 0 || start >= end {
            return;
        }
        self.param.shift_impl(start, end, shift);
        enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        self.body.shift_impl(start, end, shift);
    }

    fn shifted_impl(&self, mut start: VarIndex, mut end: VarIndex, mut shift: VarIndex) -> Self {
        let param = self.param.shifted_impl(start, end, shift);
        enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        let body = self.body.shifted_impl(start, end, shift);
        ParameterizedObject { param, body }
    }

    fn count_refs_impl(&self, mut start: VarIndex, ref_counts: &mut [usize]) {
        if ref_counts.is_empty() {
            return;
        }
        self.param.count_refs_impl(start, ref_counts);
        enter_binder_for_start::<PARAM_LEN>(&mut start);
        self.body.count_refs_impl(start, ref_counts);
    }

    fn has_refs_impl(&self, mut start: VarIndex, mut end: VarIndex) -> bool {
        if start >= end {
            return false;
        }
        if self.param.has_refs_impl(start, end) {
            return true;
        }
        enter_binder_for_start_and_end::<PARAM_LEN>(&mut start, &mut end);
        self.body.has_refs_impl(start, end)
    }
}

impl<
        SubstArg,
        Param: ContextObjectWithSubst<SubstArg>,
        Body: ContextObjectWithSubst<SubstArg>,
        const PARAM_LEN: VarIndex,
    > ContextObjectWithSubst<SubstArg> for ParameterizedObject<Param, Body, PARAM_LEN>
{
    fn substitute_impl(
        &mut self,
        mut shift_start: VarIndex,
        mut args_start: VarIndex,
        args: &mut [SubstArg],
        ref_counts: &mut [usize],
    ) {
        if args.is_empty() {
            return;
        }
        self.param
            .substitute_impl(shift_start, args_start, args, ref_counts);
        enter_binder_for_start_and_end::<PARAM_LEN>(&mut shift_start, &mut args_start);
        self.body
            .substitute_impl(shift_start, args_start, args, ref_counts);
    }
}

pub type Lambda<Param, Body> = ParameterizedObject<Param, Body, 1>;

impl<
        Ctx: ParamContext<Param>,
        Param: ContextObjectWithCmp<Ctx>,
        Body: ContextObjectWithCmp<Ctx>,
    > ContextObjectWithCmp<Ctx> for Lambda<Param, Body>
{
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if !self
            .param
            .shift_and_compare_impl(ctx, orig_ctx, &target.param, target_subctx)?
        {
            return Ok(false);
        }
        ctx.with_local(&self.param, |body_ctx| {
            target_subctx.with_local(&target.param, |target_body_ctx| {
                self.body
                    .shift_and_compare_impl(body_ctx, orig_ctx, &target.body, target_body_ctx)
            })
        })
    }
}

impl<
        SubstArg: CanBeEmpty,
        Ctx: ParamContext<Param>,
        Param: ContextObjectWithSubstCmp<SubstArg, Ctx>,
        Body: ContextObjectWithSubstCmp<SubstArg, Ctx>,
    > ContextObjectWithSubstCmp<SubstArg, Ctx> for Lambda<Param, Body>
{
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if !self.param.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.param,
            target_subctx,
        )? {
            return Ok(false);
        }
        ctx.with_local(&self.param, |body_ctx| {
            target_subctx.with_local(&target.param, |target_body_ctx| {
                self.body.substitute_and_shift_and_compare_impl(
                    body_ctx,
                    args,
                    subst_ctx,
                    &target.body,
                    target_body_ctx,
                )
            })
        })
    }
}

impl<Param: Debug, Body: Debug> Debug for Lambda<Param, Body> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("λ")?;
        self.param.fmt(f)?;
        f.write_str(".")?;
        self.body.fmt(f)
    }
}

pub type App<Fun, Arg> = ParameterizedObject<Arg, Fun, 0>;

impl<Ctx: Context, Fun: ContextObjectWithCmp<Ctx>, Arg: ContextObjectWithCmp<Ctx>>
    ContextObjectWithCmp<Ctx> for App<Fun, Arg>
{
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if !self
            .param
            .shift_and_compare_impl(ctx, orig_ctx, &target.param, target_subctx)?
        {
            return Ok(false);
        }
        self.body
            .shift_and_compare_impl(ctx, orig_ctx, &target.body, target_subctx)
    }
}

impl<
        SubstArg: CanBeEmpty,
        Ctx: Context,
        Fun: ContextObjectWithSubstCmp<SubstArg, Ctx>,
        Arg: ContextObjectWithSubstCmp<SubstArg, Ctx>,
    > ContextObjectWithSubstCmp<SubstArg, Ctx> for App<Fun, Arg>
{
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if !self.param.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.param,
            target_subctx,
        )? {
            return Ok(false);
        }
        self.body.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.body,
            target_subctx,
        )
    }
}

impl<Fun: Debug, Arg: Debug> Debug for App<Fun, Arg> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.body.fmt(f)?;
        f.write_str("(")?;
        self.param.fmt(f)?;
        f.write_str(")")
    }
}

/// A generic abstraction over `MultiLambda` and `MultiApp`. If `PARAM_LEN` is nonzero, each
/// parameter depends on the previous, and the body depends on all parameters.
#[derive(Clone, PartialEq, Default)]
pub struct MultiParameterizedObject<Param, Body, const PARAM_LEN: VarIndex> {
    pub params: InlineVec<Param>,
    pub body: Body,
}

impl<Param: ContextObject, Body: ContextObject, const PARAM_LEN: VarIndex> ContextObject
    for MultiParameterizedObject<Param, Body, PARAM_LEN>
{
    fn shift_impl(&mut self, mut start: VarIndex, mut end: VarIndex, mut shift: VarIndex) {
        if shift == 0 || start >= end {
            return;
        }
        for param in self.params.iter_mut() {
            param.shift_impl(start, end, shift);
            enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        }
        self.body.shift_impl(start, end, shift);
    }

    fn shifted_impl(&self, mut start: VarIndex, mut end: VarIndex, mut shift: VarIndex) -> Self {
        let mut params = InlineVec::with_capacity(self.params.len());
        for param in self.params.iter() {
            params.push(param.shifted_impl(start, end, shift));
            enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        }
        let body = self.body.shifted_impl(start, end, shift);
        MultiParameterizedObject { params, body }
    }

    fn count_refs_impl(&self, mut start: VarIndex, ref_counts: &mut [usize]) {
        if ref_counts.is_empty() {
            return;
        }
        for param in self.params.iter() {
            param.count_refs_impl(start, ref_counts);
            enter_binder_for_start::<PARAM_LEN>(&mut start);
        }
        self.body.count_refs_impl(start, ref_counts);
    }

    fn has_refs_impl(&self, mut start: VarIndex, mut end: VarIndex) -> bool {
        if start >= end {
            return false;
        }
        for param in self.params.iter() {
            if param.has_refs_impl(start, end) {
                return true;
            }
            enter_binder_for_start_and_end::<PARAM_LEN>(&mut start, &mut end);
        }
        self.body.has_refs_impl(start, end)
    }
}

impl<
        SubstArg,
        Param: ContextObjectWithSubst<SubstArg>,
        Body: ContextObjectWithSubst<SubstArg>,
        const PARAM_LEN: VarIndex,
    > ContextObjectWithSubst<SubstArg> for MultiParameterizedObject<Param, Body, PARAM_LEN>
{
    fn substitute_impl(
        &mut self,
        mut shift_start: VarIndex,
        mut args_start: VarIndex,
        args: &mut [SubstArg],
        ref_counts: &mut [usize],
    ) {
        if args.is_empty() {
            return;
        }
        for param in self.params.iter_mut() {
            param.substitute_impl(shift_start, args_start, args, ref_counts);
            enter_binder_for_start_and_end::<PARAM_LEN>(&mut shift_start, &mut args_start);
        }
        self.body
            .substitute_impl(shift_start, args_start, args, ref_counts);
    }
}

pub type MultiLambda<Param, Body> = MultiParameterizedObject<Param, Body, 1>;

impl<
        Ctx: ParamContext<Param>,
        Param: ContextObjectWithCmp<Ctx>,
        Body: ContextObjectWithCmp<Ctx>,
    > ContextObjectWithCmp<Ctx> for MultiLambda<Param, Body>
{
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if self.params.len() != target.params.len() {
            return Ok(false);
        }
        let mut param_idx = 0;
        for (param, target_param) in self.params.iter().zip(target.params.iter()) {
            if !ctx.with_locals(&self.params[..param_idx], |param_ctx| {
                target_subctx.with_locals(&target.params[..param_idx], |target_param_ctx| {
                    param.shift_and_compare_impl(
                        param_ctx,
                        orig_ctx,
                        target_param,
                        target_param_ctx,
                    )
                })
            })? {
                return Ok(false);
            }
            param_idx += 1;
        }
        ctx.with_locals(&self.params, |body_ctx| {
            target_subctx.with_locals(&target.params, |target_body_ctx| {
                self.body
                    .shift_and_compare_impl(body_ctx, orig_ctx, &target.body, target_body_ctx)
            })
        })
    }
}

impl<
        SubstArg: CanBeEmpty,
        Ctx: ParamContext<Param>,
        Param: ContextObjectWithSubstCmp<SubstArg, Ctx>,
        Body: ContextObjectWithSubstCmp<SubstArg, Ctx>,
    > ContextObjectWithSubstCmp<SubstArg, Ctx> for MultiLambda<Param, Body>
{
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if self.params.len() != target.params.len() {
            return Ok(false);
        }
        let mut param_idx = 0;
        for (param, target_param) in self.params.iter().zip(target.params.iter()) {
            if !ctx.with_locals(&self.params[..param_idx], |param_ctx| {
                target_subctx.with_locals(&target.params[..param_idx], |target_param_ctx| {
                    param.substitute_and_shift_and_compare_impl(
                        param_ctx,
                        args,
                        subst_ctx,
                        target_param,
                        target_param_ctx,
                    )
                })
            })? {
                return Ok(false);
            }
            param_idx += 1;
        }
        ctx.with_locals(&self.params, |body_ctx| {
            target_subctx.with_locals(&target.params, |target_body_ctx| {
                self.body.substitute_and_shift_and_compare_impl(
                    body_ctx,
                    args,
                    subst_ctx,
                    &target.body,
                    target_body_ctx,
                )
            })
        })
    }
}

impl<Param: Debug, Body: Debug> Debug for MultiLambda<Param, Body> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("λ")?;
        if self.params.len() == 1 {
            self.params[0].fmt(f)?;
        } else {
            f.write_str("(")?;
            let mut comma = false;
            for param in self.params.iter() {
                if comma {
                    f.write_str(",")?;
                }
                param.fmt(f)?;
                comma = true;
            }
            f.write_str(")")?;
        }
        f.write_str(".")?;
        self.body.fmt(f)
    }
}

pub type MultiApp<Fun, Arg> = MultiParameterizedObject<Arg, Fun, 0>;

impl<Ctx: Context, Fun: ContextObjectWithCmp<Ctx>, Arg: ContextObjectWithCmp<Ctx>>
    ContextObjectWithCmp<Ctx> for MultiApp<Fun, Arg>
{
    fn shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        orig_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if !self
            .params
            .shift_and_compare_impl(ctx, orig_ctx, &target.params, target_subctx)?
        {
            return Ok(false);
        }
        self.body
            .shift_and_compare_impl(ctx, orig_ctx, &target.body, target_subctx)
    }
}

impl<
        SubstArg: CanBeEmpty,
        Ctx: Context,
        Fun: ContextObjectWithSubstCmp<SubstArg, Ctx>,
        Arg: ContextObjectWithSubstCmp<SubstArg, Ctx>,
    > ContextObjectWithSubstCmp<SubstArg, Ctx> for MultiApp<Fun, Arg>
{
    fn substitute_and_shift_and_compare_impl(
        &self,
        ctx: &Ctx,
        args: &mut [SubstArg],
        subst_ctx: &Ctx,
        target: &Self,
        target_subctx: &Ctx,
    ) -> Result<bool> {
        if !self.params.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.params,
            target_subctx,
        )? {
            return Ok(false);
        }
        self.body.substitute_and_shift_and_compare_impl(
            ctx,
            args,
            subst_ctx,
            &target.body,
            target_subctx,
        )
    }
}

impl<Fun: Debug, Arg: Debug> Debug for MultiApp<Fun, Arg> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.body.fmt(f)?;
        f.write_str("(")?;
        let mut comma = false;
        for param in self.params.iter() {
            if comma {
                f.write_str(",")?;
            }
            param.fmt(f)?;
            comma = true;
        }
        f.write_str(")")
    }
}
