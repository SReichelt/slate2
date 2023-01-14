/// A De Bruijn level if nonnegative, or a bitwise negated De Bruijn index if negative.
///
/// We can regard nonnegative indices as referring to "globals" or "free variables", and negative
/// indices as referring to "locals" or "bound variables". Both have their uses: An expression that
/// refers to globals but is closed with respect to locals (i.e. does not have any loose bound
/// variables) can be reused without modification at all places where those globals are in scope.
///
/// So when working inside a specific context, we generally want to make sure that the condition
/// above is satisfied, which means that whenever we "enter" a binder, we need to shift the
/// variable indices referring to that binder from local to global. We can still work with arbitrary
/// subexpressions without entering the binders on the way, but then we potentially need to shift
/// their loose bound variables when substituting.
///
/// The encoding is chosen so that array indices become the most convenient. We can think of the
/// indices as referencing either the bottom or the top of the context stack:
///
/// locals  | -1
///         | -2
/// /\/\/\/\/\/\
///         |  1
/// globals |  0
///
/// Interestingly, this is exactly how array indexing works in some programming languages.
pub type VarIndex = isize;

pub const REF_CHUNK_LEN: usize = 16;

/// An object that lives in a specific context, so that variable indices are meaningful.
pub trait ContextObject: Clone {
    /// Shifts variable indices between `start` (inclusive) `end` (exclusive) by `shift`, in a way
    /// that respects the distinction between globals and locals:
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
    fn shift_vars(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex);

    /// Combination of `clone` and `shift_vars`. This may be optimized by specific implementations.
    fn with_shifted_vars(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        let mut result = self.clone();
        result.shift_vars(start, end, shift);
        result
    }

    /// For each variable in the range from `start` to `start + ref_counts.len()`, counts how often
    /// it is referenced, by increasing the corresponding item in `ref_counts`.
    fn count_refs(&self, start: VarIndex, ref_counts: &mut [usize]);

    /// Similar to `count_refs`, but just checks whether any references exist.
    fn has_refs(&self, start: VarIndex, end: VarIndex) -> bool;
}

impl ContextObject for () {
    fn shift_vars(&mut self, _: VarIndex, _: VarIndex, _: VarIndex) {}

    fn count_refs(&self, _: VarIndex, _: &mut [usize]) {}

    fn has_refs(&self, _: VarIndex, _: VarIndex) -> bool {
        false
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
    /// if `shift_start` < 0, indices smaller than `shift_start` must not exist, as in `shift_vars`.
    ///
    /// `ref_counts` should either be empty or have the same length as `args`. In the latter case,
    /// it should be the result of the corresponding call to `count_refs`. This reduces memory
    /// allocations by calling `std::mem::take` on each item in `args` when its reference count
    /// reaches 1. Otherwise, the method does not modify `args`.
    ///
    /// If the arguments have loose bound variables, they are considered to live in the target
    /// context of the substitution, i.e. their local indices are shifted up by `args.len()`, and
    /// the limit of their loose bound variables is given by
    /// `shift_start - (args_start + args.len())`.
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        ref_counts: &mut [usize],
    );

    /// Substitutes the variables in the range from `args_start` to `args_start + args.len()` with
    /// `args` (more precisely, with data provided by `args`), adjusting indices in arguments as
    /// required. Indices between `shift_start` and `args_start` are shifted up by `args.len()`, and
    /// if `shift_start` < 0, indices smaller than `shift_start` must not exist, as in `shift_vars`.
    ///
    /// `may_take_args` may be set to avoid unnecessary memory allocations in case `args` is no
    /// longer needed afterwards.
    ///
    /// If the arguments have loose bound variables, they are considered to live in the target
    /// context of the substitution, i.e. their local indices are shifted up by `args.len()`, and
    /// the limit of their loose bound variables is given by
    /// `shift_start - (args_start + args.len())`.
    fn substitute(
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
                self.count_refs(args_start, &mut ref_counts);
                let (cur_args, rest_args) = args.split_at_mut(REF_CHUNK_LEN);
                self.substitute_impl(shift_start, args_start, cur_args, &mut ref_counts);
                debug_assert_eq!(ref_counts, [0; REF_CHUNK_LEN]);
                len -= REF_CHUNK_LEN;
                shift_start += REF_CHUNK_LEN as VarIndex;
                args_start += REF_CHUNK_LEN as VarIndex;
                args = rest_args;
            }
            let rest_ref_counts = &mut ref_counts[..len];
            self.count_refs(args_start, rest_ref_counts);
            self.substitute_impl(shift_start, args_start, args, rest_ref_counts);
            debug_assert_eq!(ref_counts, [0; REF_CHUNK_LEN]);
        } else {
            self.substitute_impl(shift_start, args_start, args, &mut []);
        }
    }
}

impl<SubstArg> ContextObjectWithSubst<SubstArg> for () {
    fn substitute_impl(&mut self, _: VarIndex, _: VarIndex, _: &mut [SubstArg], _: &mut [usize]) {}
}

pub trait ContextObjectWithCmp<CmpData>: ContextObject {
    /// Checks whether the shifted expression equals `target`.
    fn shift_and_compare(
        &self,
        start: VarIndex,
        end: VarIndex,
        shift: VarIndex,
        target: &Self,
        cmp_data: &CmpData,
    ) -> bool;

    fn compare(&self, locals_start: VarIndex, target: &Self, cmp_data: &CmpData) -> bool {
        self.shift_and_compare(locals_start, 0, 0, target, cmp_data)
    }
}

impl<CmpData> ContextObjectWithCmp<CmpData> for () {
    fn shift_and_compare(
        &self,
        _: VarIndex,
        _: VarIndex,
        _: VarIndex,
        _: &Self,
        _: &CmpData,
    ) -> bool {
        true
    }
}

pub trait ContextObjectWithSubstCmp<SubstArg, CmpData>:
    ContextObjectWithSubst<SubstArg> + ContextObjectWithCmp<CmpData>
{
    /// Performs substitution like `substitute`, but compares the result against `target` instead of
    /// mutating. Arguments may optionally be omitted by setting the corresponding item of
    /// `args_filled` to `false`. Whenever such an argument is encountered during comparison, it is
    /// filled with the corresponding part of `target`, and the associated `args_filled` item is set
    /// to `true`.
    ///
    /// If `args_filled` is shorter than `args`, all remaining arguments are assumed to be filled.
    fn substitute_and_compare(
        &self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        args_filled: &mut [bool],
        target: &Self,
        cmp_data: &CmpData,
    ) -> bool;
}

impl<SubstArg, CmpData> ContextObjectWithSubstCmp<SubstArg, CmpData> for () {
    fn substitute_and_compare(
        &self,
        _: VarIndex,
        _: VarIndex,
        _: &mut [SubstArg],
        _: &mut [bool],
        _: &Self,
        _: &CmpData,
    ) -> bool {
        true
    }
}

pub trait SubstInto<SubstArg, SubstResult> {
    fn get_subst_arg(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        ref_counts: &mut [usize],
    ) -> Option<SubstResult>;
}

pub trait SubstCmpInto<SubstArg, SubstResult, CmpData> {
    fn compare_subst_arg(
        &self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [SubstArg],
        args_filled: &mut [bool],
        target: &SubstResult,
        cmp_data: &CmpData,
    ) -> Option<bool>;
}
