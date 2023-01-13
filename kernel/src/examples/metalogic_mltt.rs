use smallvec::smallvec;

use crate::{context::*, context_object::*, metalogic::*};

pub fn get_mltt() -> MetaLogic {
    MetaLogic::construct(
        &[
            ("U", "U"),
            ("Pi", "Π A : U. ((A → U) → U)"),
            ("Sigma", "Π A : U. ((A → U) → U)"),
            (
                "Sigma_intro",
                "Π A : U. Π P : A → U. Π a : A. (P a → Sigma A P)",
            ),
            ("Sigma_fst", "Π A : U. Π P : A → U. (Sigma A P → A)"),
            (
                "Sigma_snd",
                "Π A : U. Π P : A → U. Π p : Sigma A P. P (Sigma_fst A P p)",
            ),
            ("pair", "Π A B : U. (A → B → (A × B))"),
            ("pair_fst", "Π A B : U. ((A × B) → A)"),
            ("pair_snd", "Π A B : U. ((A × B) → B)"),
        ],
        &[
            (
                &[("A", "U"), ("P", "A → U"), ("a", "A"), ("b", "P a")],
                "Sigma_fst A P (Sigma_intro A P a b)",
                "a",
            ),
            (
                &[("A", "U"), ("P", "A → U"), ("a", "A"), ("b", "P a")],
                "Sigma_snd A P (Sigma_intro A P a b)",
                "b",
            ),
            (
                &[("A", "U"), ("B", "U")],
                "pair A B",
                "Sigma_intro A (λ a : A. B)",
            ),
            (
                &[("A", "U"), ("B", "U")],
                "pair_fst A B",
                "Sigma_fst A (λ a : A. B)",
            ),
            (
                &[("A", "U"), ("B", "U")],
                "pair_snd A B",
                "Sigma_snd A (λ a : A. B)",
            ),
        ],
        |ctx| Box::new(MLTTLambdaHandler::new(ctx)),
    )
    .unwrap()
}

struct MLTTLambdaHandler {
    u_idx: VarIndex,
    pi_idx: VarIndex,
    sigma_idx: VarIndex,
}

impl MLTTLambdaHandler {
    fn new(ctx: &Context<Param>) -> Self {
        MLTTLambdaHandler {
            u_idx: ctx.get_var_index("U").unwrap(),
            pi_idx: ctx.get_var_index("Pi").unwrap(),
            sigma_idx: ctx.get_var_index("Sigma").unwrap(),
        }
    }
}

impl LambdaHandler for MLTTLambdaHandler {
    fn get_universe_type(&self) -> Result<Expr, String> {
        Ok(Expr::var(self.u_idx))
    }

    fn get_dep_type(
        &self,
        domain: Expr,
        prop: Expr,
        kind: DependentTypeCtorKind,
        _: &Context<Param>,
    ) -> Result<Expr, String> {
        let idx = match kind {
            DependentTypeCtorKind::Pi => self.pi_idx,
            DependentTypeCtorKind::Sigma => self.sigma_idx,
        };
        Ok(Expr::multi_app(Expr::var(idx), smallvec![domain, prop]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basics() {
        let mltt = get_mltt();
        let root_ctx = mltt.get_root_context();

        let pi = mltt.get_constant("Pi").unwrap();
        assert_eq!(
            mltt.print_expr(&pi.type_expr, &root_ctx),
            "Π A : U. ((A → U) → U)"
        );

        let id_ctor = mltt.parse_expr("λ A : U. A", &root_ctx).unwrap();
        assert_eq!(mltt.print_expr(&id_ctor, &root_ctx), "λ A : U. A");
        let id_ctor_type = mltt.get_expr_type(&id_ctor, &root_ctx).unwrap();
        assert_eq!(mltt.print_expr(&id_ctor_type, &root_ctx), "U → U");

        let const_ctor = mltt.parse_expr("λ A B : U. A", &root_ctx).unwrap();
        assert_eq!(mltt.print_expr(&const_ctor, &root_ctx), "λ A : U. λ B : U. A");
        let const_ctor_type = mltt.get_expr_type(&const_ctor, &root_ctx).unwrap();
        assert_eq!(mltt.print_expr(&const_ctor_type, &root_ctx), "U → U → U");

        let app_u = mltt.parse_expr("λ F : U → U. F U", &root_ctx).unwrap();
        let app_u_type = mltt.get_expr_type(&app_u, &root_ctx).unwrap();
        assert_eq!(mltt.print_expr(&app_u_type, &root_ctx), "(U → U) → U");

        let id_fun = mltt.parse_expr("λ A : U. λ a : A. a", &root_ctx).unwrap();
        let id_fun_type = mltt.get_expr_type(&id_fun, &root_ctx).unwrap();
        assert_eq!(mltt.print_expr(&id_fun_type, &root_ctx), "Π A : U. (A → A)");

        let inner_const_fun = mltt.parse_expr("λ A : U. λ a b : A. a", &root_ctx).unwrap();
        assert_eq!(mltt.print_expr(&inner_const_fun, &root_ctx), "λ A : U. λ a : A. λ b : A. a");
        let inner_const_fun_type = mltt.get_expr_type(&inner_const_fun, &root_ctx).unwrap();
        assert_eq!(mltt.print_expr(&inner_const_fun_type, &root_ctx), "Π A : U. (A → A → A)");

        let pair_fun = mltt
            .parse_expr("λ A B : U. λ a : A. λ b : B. pair A B a b", &root_ctx)
            .unwrap();
        let pair_fun_type = mltt.get_expr_type(&pair_fun, &root_ctx).unwrap();
        assert_eq!(
            mltt.print_expr(&pair_fun_type, &root_ctx),
            "Π A : U. Π B : U. (A → B → (A × B))"
        );
    }

    #[test]
    fn test_type_errors() {
        let mltt = get_mltt();
        let root_ctx = mltt.get_root_context();

        let non_fun_app = mltt.parse_expr("λ A : U. A A", &root_ctx).unwrap();
        assert!(mltt.get_expr_type(&non_fun_app, &root_ctx).is_err());

        let app_mismatch = mltt.parse_expr("λ F : U → U. F F", &root_ctx).unwrap();
        assert!(mltt.get_expr_type(&app_mismatch, &root_ctx).is_err());
    }

    #[test]
    fn test_type_of_types() {
        let mltt = get_mltt();
        mltt.check_type_of_types().unwrap();
    }

    #[test]
    fn test_reduction_rule_types() {
        let mltt = get_mltt();
        mltt.check_reduction_rule_types().unwrap();
    }

    // TODO: test that all declared types reduce uniquely (are confluent)
    // TODO test that specific known terms with multiple reductions are confluent
}
