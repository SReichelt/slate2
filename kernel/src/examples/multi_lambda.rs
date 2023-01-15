//! A variant of untyped lambda calculus that matches the substitution mechanisms in Slate more
//! closely than regular lambda calculus. We use this to unit-test the substitution code.
//!
//! There are just two primitive expression types, which suffice to express all irreducible
//! expressions (and only those):
//! * lambda abstractions (with arbitrarily many parameters, because the substitution code tends to
//!   deal with parameter lists instead of single parameters), and
//! * variable references with arbitrarily many argument lists (combining variable references with
//!   application).
//!
//! We then add let-bindings at top level only, i.e. we add the concept of definitions, thereby
//! introducing reduction as unfolding of these definitions (or equivalently beta reduction of
//! let-bindings). However, in contrast to regular lambda calculus, multiple substitutions may be
//! required for each variable reference that is replaced, if that variable reference contains one
//! or more argument lists:
//! * If the substituted term is a lambda abstraction, then the first argument list must be applied
//!   to that lambda abstraction immediately. We require the length of both lists to match exactly.
//!   Afterwards, the resulting expression must be applied to the remaining argument lists in the
//!   same way.
//! * If the substituted term is a variable reference, then the argument lists must be combined.
//!
//! This modified lambda calculus is equivalent to regular lambda calculus; e.g. consider that the
//! combinators S, K, and I can be defined as let-bindings. (Of course, being equivalent really just
//! means it is Turing-complete.)

use std::fmt::Debug;

use smallvec::{smallvec, SmallVec};

use crate::generic::{context::*, context_object::*, expr::*};

#[derive(Clone, PartialEq)]
pub enum InnerExpr {
    Lambda(Box<MultiLambda<(), InnerExpr>>),
    VarApp(VarApp),
}

#[derive(Clone, PartialEq)]
pub enum VarApp {
    Var(Var),
    App(Box<MultiApp<VarApp, InnerExpr>>),
}

pub type OuterExpr = MultiLambda<InnerExpr, InnerExpr>;

impl InnerExpr {
    pub fn lambda(params: usize, body: InnerExpr) -> Self {
        InnerExpr::Lambda(Box::new(MultiLambda {
            params: smallvec![(); params],
            body,
        }))
    }

    pub fn var(idx: VarIndex) -> Self {
        InnerExpr::VarApp(VarApp::var(idx))
    }

    pub fn var_app(idx: VarIndex, args: Vec<SmallVec<[InnerExpr; INLINE_PARAMS]>>) -> Self {
        InnerExpr::VarApp(VarApp::var_app(idx, args))
    }
}

impl Default for InnerExpr {
    fn default() -> Self {
        InnerExpr::VarApp(VarApp::default())
    }
}

impl Debug for InnerExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Lambda(lambda) => lambda.fmt(f),
            Self::VarApp(var_app) => var_app.fmt(f),
        }
    }
}

impl ContextObject for InnerExpr {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        match self {
            InnerExpr::Lambda(lambda) => lambda.shift_impl(start, end, shift),
            InnerExpr::VarApp(var_app) => var_app.shift_impl(start, end, shift),
        }
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        match self {
            InnerExpr::Lambda(lambda) => {
                InnerExpr::Lambda(Box::new(lambda.shifted_impl(start, end, shift)))
            }
            InnerExpr::VarApp(var_app) => {
                InnerExpr::VarApp(var_app.shifted_impl(start, end, shift))
            }
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        match self {
            InnerExpr::Lambda(lambda) => lambda.count_refs_impl(start, ref_counts),
            InnerExpr::VarApp(var_app) => var_app.count_refs_impl(start, ref_counts),
        }
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        match self {
            InnerExpr::Lambda(lambda) => lambda.has_refs_impl(start, end),
            InnerExpr::VarApp(var_app) => var_app.has_refs_impl(start, end),
        }
    }
}

impl ContextObjectWithSubst<InnerExpr> for InnerExpr {
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [InnerExpr],
        ref_counts: &mut [usize],
    ) {
        match self {
            InnerExpr::Lambda(lambda) => {
                lambda.substitute_impl(shift_start, args_start, args, ref_counts)
            }
            InnerExpr::VarApp(var_app) => {
                if let Some(subst_arg) =
                    var_app.get_subst_arg_impl(shift_start, args_start, args, ref_counts)
                {
                    *self = subst_arg;
                } else {
                    var_app.substitute_impl(shift_start, args_start, args, ref_counts);
                }
            }
        }
    }
}

impl VarApp {
    pub fn var(idx: VarIndex) -> Self {
        VarApp::Var(Var(idx))
    }

    pub fn var_app(idx: VarIndex, args: Vec<SmallVec<[InnerExpr; INLINE_PARAMS]>>) -> Self {
        let mut result = VarApp::var(idx);
        for arg in args {
            result = VarApp::App(Box::new(MultiApp {
                params: arg,
                body: result,
            }))
        }
        result
    }
}

impl Default for VarApp {
    fn default() -> Self {
        VarApp::Var(Var::default())
    }
}

impl Debug for VarApp {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Var(var) => var.fmt(f),
            Self::App(app) => app.fmt(f),
        }
    }
}

impl ContextObject for VarApp {
    fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
        match self {
            VarApp::Var(var) => var.shift_impl(start, end, shift),
            VarApp::App(app) => app.shift_impl(start, end, shift),
        }
    }

    fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
        match self {
            VarApp::Var(var) => VarApp::Var(var.shifted_impl(start, end, shift)),
            VarApp::App(app) => VarApp::App(Box::new(app.shifted_impl(start, end, shift))),
        }
    }

    fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
        match self {
            VarApp::Var(var) => var.count_refs_impl(start, ref_counts),
            VarApp::App(app) => app.count_refs_impl(start, ref_counts),
        }
    }

    fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
        match self {
            VarApp::Var(var) => var.has_refs_impl(start, end),
            VarApp::App(app) => app.has_refs_impl(start, end),
        }
    }
}

impl ContextObjectWithSubst<InnerExpr> for VarApp {
    fn substitute_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [InnerExpr],
        ref_counts: &mut [usize],
    ) {
        match self {
            VarApp::Var(var) => var.shift_impl(shift_start, args_start, args.len() as VarIndex),
            VarApp::App(app) => app.substitute_impl(shift_start, args_start, args, ref_counts),
        }
    }
}

impl SubstInto<InnerExpr, InnerExpr> for VarApp {
    fn get_subst_arg_impl(
        &mut self,
        shift_start: VarIndex,
        args_start: VarIndex,
        args: &mut [InnerExpr],
        ref_counts: &mut [usize],
    ) -> Option<InnerExpr> {
        match self {
            VarApp::Var(var) => var.get_subst_arg_impl(shift_start, args_start, args, ref_counts),
            VarApp::App(app) => {
                let subst_arg =
                    app.body
                        .get_subst_arg_impl(shift_start, args_start, args, ref_counts)?;
                for app_arg in app.params.iter_mut() {
                    app_arg.substitute_impl(shift_start, args_start, args, ref_counts);
                }
                let result = match subst_arg {
                    InnerExpr::Lambda(mut lambda) => {
                        let params_len = lambda.params.len();
                        let app_args_len = app.params.len();
                        if params_len != app_args_len {
                            panic!("expected {params_len} argument(s) but got {app_args_len}");
                        }
                        // See comment at substitute_impl.
                        let args_end = args_start + args.len() as VarIndex;
                        let lambda_shift_start = shift_start - args_end;
                        let app_args_start = -(app_args_len as VarIndex);
                        lambda.body.substitute_int(
                            lambda_shift_start + app_args_start,
                            app_args_start,
                            &mut app.params,
                            true,
                        );
                        lambda.body
                    }
                    InnerExpr::VarApp(var_app) => {
                        app.body = var_app;
                        InnerExpr::VarApp(VarApp::App(std::mem::take(app)))
                    }
                };
                Some(result)
            }
        }
    }
}

impl OuterExpr {
    pub fn reduce(mut self) -> InnerExpr {
        // First substitute earlier variables within later ones, then substitute everything at once
        // in the body.
        // Although it would be easier to substitute the variables from last to first within the
        // body only, we take the more complicated route because we need to do something similar in
        // a real application.
        let len = self.params.len();
        for i in 1..len {
            let (prev_params, rest) = self.params.split_at_mut(i);
            let param = &mut rest[0];
            let start = -(i as VarIndex);
            param.substitute_int(start, start, prev_params, false);
        }
        self.body
            .substitute(&mut self.params, true, &MinimalContext::new());
        self.body
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_id() -> InnerExpr {
        // λx.x
        InnerExpr::lambda(1, InnerExpr::var(-1))
    }

    #[test]
    fn test_id() {
        let expr = OuterExpr {
            // let I = λx.x
            params: smallvec![get_id()],
            // in I
            body: InnerExpr::var(-1),
        };
        assert_eq!(
            expr.reduce(),
            // λx.x
            get_id()
        );
    }

    #[test]
    fn test_id_id() {
        let expr = OuterExpr {
            // let I = λx.x
            params: smallvec![get_id()],
            // in I(I)
            body: InnerExpr::var_app(-1, vec![smallvec![InnerExpr::var(-1)]]),
        };
        assert_eq!(
            expr.reduce(),
            // λx.x
            get_id()
        );
    }

    #[test]
    fn test_id_id_2() {
        let expr = OuterExpr {
            params: smallvec![
                // let I = λx.x
                get_id(),
                // let J = λx.x
                get_id(),
            ],
            // in I(J)
            body: InnerExpr::var_app(-2, vec![smallvec![InnerExpr::var(-1)]]),
        };
        assert_eq!(
            expr.reduce(),
            // λx.x
            get_id()
        );
    }

    #[test]
    fn test_id_id_id() {
        let expr = OuterExpr {
            // let I = λx.x
            params: smallvec![get_id()],
            // in I(I)(I)
            body: InnerExpr::var_app(
                -1,
                vec![smallvec![InnerExpr::var(-1)], smallvec![InnerExpr::var(-1)]],
            ),
        };
        assert_eq!(
            expr.reduce(),
            // λx.x
            get_id()
        );
    }

    #[test]
    fn test_id_id_id_nested() {
        let expr = OuterExpr {
            // let I = λx.x
            params: smallvec![get_id()],
            // in I(I(I))
            body: InnerExpr::var_app(
                -1,
                vec![smallvec![InnerExpr::var_app(
                    -1,
                    vec![smallvec![InnerExpr::var(-1)]]
                )]],
            ),
        };
        assert_eq!(
            expr.reduce(),
            // λx.x
            get_id()
        );
    }

    #[test]
    #[should_panic(expected = "expected 1 argument(s) but got 2")]
    fn test_wrong_arg_len() {
        let expr = OuterExpr {
            // let I = λx.x
            params: smallvec![get_id()],
            // I(I,I)
            body: InnerExpr::var_app(-1, vec![smallvec![InnerExpr::var(-1), InnerExpr::var(-1)]]),
        };
        expr.reduce();
    }

    fn get_omega() -> InnerExpr {
        // λf.f(f)
        InnerExpr::lambda(
            1,
            InnerExpr::var_app(-1, vec![smallvec![InnerExpr::var(-1)]]),
        )
    }

    #[test]
    fn test_omega() {
        let expr = OuterExpr {
            // let ω = λf.f(f)
            params: smallvec![get_omega()],
            // in ω  (note that ω(ω) would cause an infinite recursion)
            body: InnerExpr::var(-1),
        };
        assert_eq!(
            expr.reduce(),
            // λf.f(f)
            get_omega()
        );
    }

    fn get_mul() -> InnerExpr {
        // λ(m,n).λ(f,x).m(λy.n(f,y),x)
        InnerExpr::lambda(
            2,
            InnerExpr::lambda(
                2,
                InnerExpr::var_app(
                    -4,
                    vec![smallvec![
                        InnerExpr::lambda(
                            1,
                            InnerExpr::var_app(
                                -4,
                                vec![smallvec![InnerExpr::var(-3), InnerExpr::var(-1)]]
                            ),
                        ),
                        InnerExpr::var(-1),
                    ]],
                ),
            ),
        )
    }

    fn get_num(n: usize) -> InnerExpr {
        // λ(f,x).f(...(f(x)))
        let mut result = InnerExpr::var(-1);
        for _ in 0..n {
            result = InnerExpr::var_app(-2, vec![smallvec![result]]);
        }
        InnerExpr::lambda(2, result)
    }

    #[test]
    fn test_mul_1_1() {
        let expr = OuterExpr {
            params: smallvec![
                // let * = λ(m,n).λ(f,x).m(λy.n(f,y),x)
                get_mul(),
                // let 1 = λ(f,x).f(x)
                get_num(1),
            ],
            // in *(1,1)
            body: InnerExpr::var_app(-2, vec![smallvec![InnerExpr::var(-1), InnerExpr::var(-1)]]),
        };
        assert_eq!(
            expr.reduce(),
            // λ(f,x).f(x)
            get_num(1)
        );
    }

    #[test]
    fn test_mul_1_2() {
        let expr = OuterExpr {
            params: smallvec![
                // let * = λ(m,n).λ(f,x).m(λy.n(f,y),x)
                get_mul(),
                // let 1 = λ(f,x).f(x)
                get_num(1),
                // let 2 = λ(f,x).f(f(x))
                get_num(2),
            ],
            // in *(1,2)
            body: InnerExpr::var_app(-3, vec![smallvec![InnerExpr::var(-2), InnerExpr::var(-1)]]),
        };
        assert_eq!(
            expr.reduce(),
            // λ(f,x).f(f(x))
            get_num(2)
        );
    }

    #[test]
    fn test_mul_2_1() {
        let expr = OuterExpr {
            params: smallvec![
                // let * = λ(m,n).λ(f,x).m(λy.n(f,y),x)
                get_mul(),
                // let 1 = λ(f,x).f(x)
                get_num(1),
                // let 2 = λ(f,x).f(f(x))
                get_num(2),
            ],
            // in *(2,1)
            body: InnerExpr::var_app(-3, vec![smallvec![InnerExpr::var(-1), InnerExpr::var(-2)]]),
        };
        assert_eq!(
            expr.reduce(),
            // λ(f,x).f(f(x))
            get_num(2)
        );
    }

    #[test]
    fn test_mul_2_2() {
        let expr = OuterExpr {
            params: smallvec![
                // let * = λ(m,n).λ(f,x).m(λy.n(f,y),x)
                get_mul(),
                // let 2 = λ(f,x).f(f(x))
                get_num(2),
            ],
            // in *(2,2)
            body: InnerExpr::var_app(-2, vec![smallvec![InnerExpr::var(-1), InnerExpr::var(-1)]]),
        };
        assert_eq!(
            expr.reduce(),
            // λ(f,x).f(f(f(f(x)))
            get_num(4)
        );
    }

    #[test]
    fn test_mul_2_3() {
        let expr = OuterExpr {
            params: smallvec![
                // let * = λ(m,n).λ(f,x).m(λy.n(f,y),x)
                get_mul(),
                // let 2 = λ(f,x).f(f(x))
                get_num(2),
                // let 3 = λ(f,x).f(f(f(x)))
                get_num(3),
            ],
            // in *(2,3)
            body: InnerExpr::var_app(-3, vec![smallvec![InnerExpr::var(-2), InnerExpr::var(-1)]]),
        };
        assert_eq!(
            expr.reduce(),
            // λ(f,x).f(f(f(f(f(f(x))))))
            get_num(6)
        );
    }

    #[test]
    fn test_mul_2_3_permut() {
        let expr = OuterExpr {
            params: smallvec![
                // let 2 = λ(f,x).f(f(x))
                get_num(2),
                // let 3 = λ(f,x).f(f(f(x)))
                get_num(3),
                // let * = λ(m,n).λ(f,x).m(λy.n(f,y),x)
                get_mul(),
            ],
            // in *(2,3)
            body: InnerExpr::var_app(-1, vec![smallvec![InnerExpr::var(-3), InnerExpr::var(-2)]]),
        };
        assert_eq!(
            expr.reduce(),
            // λ(f,x).f(f(f(f(f(f(x))))))
            get_num(6)
        );
    }

    #[test]
    fn test_mul_2_2_2() {
        let expr = OuterExpr {
            params: smallvec![
                // let * = λ(m,n).λ(f,x).m(λy.n(f,y),x)
                get_mul(),
                // let 2 = λ(f,x).f(f(x))
                get_num(2),
                // let 4 = *(2,2)
                InnerExpr::var_app(-2, vec![smallvec![InnerExpr::var(-1), InnerExpr::var(-1)]]),
            ],
            // in *(2,4)
            body: InnerExpr::var_app(-3, vec![smallvec![InnerExpr::var(-2), InnerExpr::var(-1)]]),
        };
        assert_eq!(
            expr.reduce(),
            // λ(f,x).f(f(f(f(f(f(f(f(x))))))))
            get_num(8)
        );
    }

    fn get_app_n(n: usize) -> InnerExpr {
        // λ(f_1,...,f_n).λx.f_1(...(f_n(x)))
        let mut result = InnerExpr::var(-1);
        for i in 0..n {
            result = InnerExpr::var_app(-2 - i as VarIndex, vec![smallvec![result]]);
        }
        InnerExpr::lambda(n, InnerExpr::lambda(1, result))
    }

    fn get_succ() -> InnerExpr {
        // λn.λ(f,x).f(n(f,x))
        InnerExpr::lambda(
            1,
            InnerExpr::lambda(
                2,
                InnerExpr::var_app(
                    -2,
                    vec![smallvec![InnerExpr::var_app(
                        -3,
                        vec![smallvec![InnerExpr::var(-2), InnerExpr::var(-1)]],
                    )]],
                ),
            ),
        )
    }

    fn test_subst_chunk_impl(n: usize) {
        let expr = OuterExpr {
            params: smallvec![
                // let a = λ(f_1,...,f_n).λx.f_1(...(f_n(x)))
                get_app_n(n),
                // let s = λn.λ(f,x).f(n(f,x))
                get_succ(),
                // let 0 = λ(f,x).x
                get_num(0),
            ],
            // in a(s,...,s)(0)
            body: InnerExpr::var_app(
                -3,
                vec![
                    smallvec![InnerExpr::var(-2); n],
                    smallvec![InnerExpr::var(-1)],
                ],
            ),
        };
        assert_eq!(
            expr.reduce(),
            // λ(f,x).f(...(f(x)))
            get_num(n)
        );
    }

    #[test]
    fn test_subst_chunk() {
        test_subst_chunk_impl(1);
        test_subst_chunk_impl(REF_CHUNK_LEN);
        test_subst_chunk_impl(REF_CHUNK_LEN + 1);
        test_subst_chunk_impl(2 * REF_CHUNK_LEN);
        test_subst_chunk_impl(2 * REF_CHUNK_LEN + 1);
    }
}
