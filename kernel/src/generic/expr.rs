use std::fmt::Debug;

use smallvec::SmallVec;

use super::context_object::*;

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
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let Var(idx) = *self;
        write!(f, "#{idx}")
    }
}

impl ContextObject for Var {
    fn shift_vars(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
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

    fn count_refs(&self, start: VarIndex, ref_counts: &mut [usize]) {
        let Var(idx) = *self;
        if idx >= start {
            let end = start + ref_counts.len() as VarIndex;
            if idx < end {
                let array_idx = (idx - start) as usize;
                ref_counts[array_idx] += 1;
            }
        }
    }

    fn has_refs(&self, start: VarIndex, end: VarIndex) -> bool {
        let Var(idx) = *self;
        idx >= start && idx < end
    }
}

impl<CmpData> ContextObjectWithCmp<CmpData> for Var {
    fn shift_and_compare(
        &self,
        start: VarIndex,
        end: VarIndex,
        shift: VarIndex,
        target: &Self,
        _: &CmpData,
    ) -> bool {
        let Var(mut idx) = *self;
        if idx < start {
            if start < 0 {
                panic!("unexpected loose bound variable with index {idx} (start: {start})");
            }
        } else if idx < end {
            idx += shift;
        } else if idx < end + shift && start + shift < 0
        // implies shift > 0 and start < 0
        {
            return false;
        }
        let Var(target_idx) = *target;
        idx == target_idx
    }
}

impl<SubstArg: ContextObject + Default> SubstInto<SubstArg, SubstArg> for Var {
    fn get_subst_arg(
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
            let args_end = args_start + args.len() as VarIndex;
            if idx < args_end {
                let array_idx = (idx - args_start) as usize;
                let arg = &mut args[array_idx];
                if array_idx < ref_counts.len() {
                    let ref_count = &mut ref_counts[array_idx];
                    *ref_count -= 1;
                    if *ref_count == 0 {
                        if shift_start < 0 {
                            arg.shift_vars(shift_start - args_end, 0, args_end);
                        }
                        return Some(std::mem::take(arg));
                    }
                }
                if shift_start < 0 {
                    return Some(arg.with_shifted_vars(shift_start - args_end, 0, args_end));
                } else {
                    return Some(arg.clone());
                }
            }
        }
        None
    }
}

impl<SubstArg: ContextObjectWithCmp<CmpData> + Default, CmpData>
    SubstCmpInto<SubstArg, SubstArg, CmpData> for Var
{
    fn compare_subst_arg(
        &self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        args_filled: &mut [bool],
        target: &SubstArg,
        cmp_data: &CmpData,
    ) -> Option<bool> {
        let Var(idx) = *self;
        if idx < shift_start {
            if shift_start < 0 {
                panic!("unexpected loose bound variable with index {idx} (start: {shift_start})");
            }
        } else if idx >= args_start {
            let args_end = args_start + args.len() as VarIndex;
            if idx < args_end {
                let array_idx = (idx - args_start) as usize;
                let arg = &mut args[array_idx];
                if array_idx < args_filled.len() {
                    let filled = &mut args_filled[array_idx];
                    if !*filled {
                        if target.has_refs(args_end, 0) {
                            return Some(false);
                        }
                        *filled = true;
                        *arg = target.with_shifted_vars(shift_start, args_end, -args_end);
                        return Some(true);
                    }
                }
                return Some(arg.shift_and_compare(
                    shift_start - args_end,
                    0,
                    args_end,
                    target,
                    cmp_data,
                ));
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
    fn shift_vars(&mut self, mut start: VarIndex, mut end: VarIndex, mut shift: VarIndex) {
        if shift == 0 || start >= end {
            return;
        }
        self.param.shift_vars(start, end, shift);
        enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        self.body.shift_vars(start, end, shift);
    }

    fn with_shifted_vars(
        &self,
        mut start: VarIndex,
        mut end: VarIndex,
        mut shift: VarIndex,
    ) -> Self {
        let param = self.param.with_shifted_vars(start, end, shift);
        enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        let body = self.body.with_shifted_vars(start, end, shift);
        ParameterizedObject { param, body }
    }

    fn count_refs(&self, mut start: VarIndex, ref_counts: &mut [usize]) {
        if ref_counts.is_empty() {
            return;
        }
        self.param.count_refs(start, ref_counts);
        enter_binder_for_start::<PARAM_LEN>(&mut start);
        self.body.count_refs(start, ref_counts);
    }

    fn has_refs(&self, mut start: VarIndex, mut end: VarIndex) -> bool {
        if start >= end {
            return false;
        }
        if self.param.has_refs(start, end) {
            return true;
        }
        enter_binder_for_start_and_end::<PARAM_LEN>(&mut start, &mut end);
        self.body.has_refs(start, end)
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

impl<
        CmpData,
        Param: ContextObjectWithCmp<CmpData>,
        Body: ContextObjectWithCmp<CmpData>,
        const PARAM_LEN: VarIndex,
    > ContextObjectWithCmp<CmpData> for ParameterizedObject<Param, Body, PARAM_LEN>
{
    fn shift_and_compare(
        &self,
        mut start: VarIndex,
        mut end: VarIndex,
        mut shift: VarIndex,
        target: &Self,
        cmp_data: &CmpData,
    ) -> bool {
        if !self
            .param
            .shift_and_compare(start, end, shift, &target.param, cmp_data)
        {
            return false;
        }
        enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        self.body
            .shift_and_compare(start, end, shift, &target.body, cmp_data)
    }
}

impl<
        SubstArg,
        CmpData,
        Param: ContextObjectWithSubstCmp<SubstArg, CmpData>,
        Body: ContextObjectWithSubstCmp<SubstArg, CmpData>,
        const PARAM_LEN: VarIndex,
    > ContextObjectWithSubstCmp<SubstArg, CmpData> for ParameterizedObject<Param, Body, PARAM_LEN>
{
    fn substitute_and_compare(
        &self,
        mut shift_start: VarIndex,
        mut args_start: VarIndex,
        args: &mut [SubstArg],
        args_filled: &mut [bool],
        target: &Self,
        cmp_data: &CmpData,
    ) -> bool {
        if !self.param.substitute_and_compare(
            shift_start,
            args_start,
            args,
            args_filled,
            &target.param,
            cmp_data,
        ) {
            return false;
        }
        enter_binder_for_start_and_end::<PARAM_LEN>(&mut shift_start, &mut args_start);
        self.body.substitute_and_compare(
            shift_start,
            args_start,
            args,
            args_filled,
            &target.body,
            cmp_data,
        )
    }
}

pub type Lambda<Param, Body> = ParameterizedObject<Param, Body, 1>;
pub type App<Fun, Arg> = ParameterizedObject<Arg, Fun, 0>;

impl<Param: Debug, Body: Debug> Debug for Lambda<Param, Body> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("λ")?;
        self.param.fmt(f)?;
        f.write_str(".")?;
        self.body.fmt(f)
    }
}

impl<Fun: Debug, Arg: Debug> Debug for App<Fun, Arg> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.param.fmt(f)?;
        f.write_str("(")?;
        self.body.fmt(f)?;
        f.write_str(")")
    }
}

pub const INLINE_PARAMS: usize = 8;

/// A generic abstraction over `MultiLambda` and `MultiApp`. If `PARAM_LEN` is nonzero, each
/// parameter depends on the previous, and the body depends on all parameters.
#[derive(Clone, PartialEq, Default)]
pub struct MultiParameterizedObject<Param, Body, const PARAM_LEN: VarIndex> {
    pub params: SmallVec<[Param; INLINE_PARAMS]>,
    pub body: Body,
}

impl<Param: ContextObject, Body: ContextObject, const PARAM_LEN: VarIndex> ContextObject
    for MultiParameterizedObject<Param, Body, PARAM_LEN>
{
    fn shift_vars(&mut self, mut start: VarIndex, mut end: VarIndex, mut shift: VarIndex) {
        if shift == 0 || start >= end {
            return;
        }
        for param in self.params.iter_mut() {
            param.shift_vars(start, end, shift);
            enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        }
        self.body.shift_vars(start, end, shift);
    }

    fn with_shifted_vars(
        &self,
        mut start: VarIndex,
        mut end: VarIndex,
        mut shift: VarIndex,
    ) -> Self {
        let mut params = SmallVec::with_capacity(self.params.len());
        for param in self.params.iter() {
            params.push(param.with_shifted_vars(start, end, shift));
            enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        }
        let body = self.body.with_shifted_vars(start, end, shift);
        MultiParameterizedObject { params, body }
    }

    fn count_refs(&self, mut start: VarIndex, ref_counts: &mut [usize]) {
        if ref_counts.is_empty() {
            return;
        }
        for param in self.params.iter() {
            param.count_refs(start, ref_counts);
            enter_binder_for_start::<PARAM_LEN>(&mut start);
        }
        self.body.count_refs(start, ref_counts);
    }

    fn has_refs(&self, mut start: VarIndex, mut end: VarIndex) -> bool {
        if start >= end {
            return false;
        }
        for param in self.params.iter() {
            if param.has_refs(start, end) {
                return true;
            }
            enter_binder_for_start_and_end::<PARAM_LEN>(&mut start, &mut end);
        }
        self.body.has_refs(start, end)
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

impl<
        CmpData,
        Param: ContextObjectWithCmp<CmpData>,
        Body: ContextObjectWithCmp<CmpData>,
        const PARAM_LEN: VarIndex,
    > ContextObjectWithCmp<CmpData> for MultiParameterizedObject<Param, Body, PARAM_LEN>
{
    fn shift_and_compare(
        &self,
        mut start: VarIndex,
        mut end: VarIndex,
        mut shift: VarIndex,
        target: &Self,
        cmp_data: &CmpData,
    ) -> bool {
        if self.params.len() != target.params.len() {
            return false;
        }
        for (param, target_param) in self.params.iter().zip(target.params.iter()) {
            if !param.shift_and_compare(start, end, shift, target_param, cmp_data) {
                return false;
            }
            enter_binder_for_shift::<PARAM_LEN>(&mut start, &mut end, &mut shift);
        }
        self.body
            .shift_and_compare(start, end, shift, &target.body, cmp_data)
    }
}

impl<
        SubstArg,
        CmpData,
        Param: ContextObjectWithSubstCmp<SubstArg, CmpData>,
        Body: ContextObjectWithSubstCmp<SubstArg, CmpData>,
        const PARAM_LEN: VarIndex,
    > ContextObjectWithSubstCmp<SubstArg, CmpData>
    for MultiParameterizedObject<Param, Body, PARAM_LEN>
{
    fn substitute_and_compare(
        &self,
        mut shift_start: VarIndex,
        mut args_start: VarIndex,
        args: &mut [SubstArg],
        args_filled: &mut [bool],
        target: &Self,
        cmp_data: &CmpData,
    ) -> bool {
        if self.params.len() != target.params.len() {
            return false;
        }
        for (param, target_param) in self.params.iter().zip(target.params.iter()) {
            if !param.substitute_and_compare(
                shift_start,
                args_start,
                args,
                args_filled,
                target_param,
                cmp_data,
            ) {
                return false;
            }
            enter_binder_for_start_and_end::<PARAM_LEN>(&mut shift_start, &mut args_start);
        }
        self.body.substitute_and_compare(
            shift_start,
            args_start,
            args,
            args_filled,
            &target.body,
            cmp_data,
        )
    }
}

pub type MultiLambda<Param, Body> = MultiParameterizedObject<Param, Body, 1>;
pub type MultiApp<Fun, Arg> = MultiParameterizedObject<Arg, Fun, 0>;

impl<Param: Debug, Body: Debug> Debug for MultiLambda<Param, Body> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
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

impl<Fun: Debug, Arg: Debug> Debug for MultiApp<Fun, Arg> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
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
