use smallvec::smallvec;

use crate::{
    generic::context::*,
    metalogic::{expr::*, helpers::*, metalogic::*},
};

pub fn get_mltt() -> MetaLogic {
    MetaLogic::construct_semantically(
        &[
            TypeInit {
                ctor: ("U", "U"),
                intro: &[],
                elim: &[],
                red: &[],
            },
            TypeInit {
                ctor: ("Pi", "Π A : U. ((A → U) → U)"),
                intro: &[
                    ("id", "Π A : U. (A → A)"),
                    ("const", "Π A B : U. (B → (A → B))"),
                    ("subst", "Π A : U. Π P : A → U. Π Q : (Π a : A. (P a → U)). ((Π a : A. Pi (P a) (Q a)) → Π f : Pi A P. Π a : A. Q a (f a))"),
                ],
                elim: &[],
                red: &[
                    (&[("A", "U"), ("a", "A")], "id A a", "a"),
                    (
                        &[("A", "U"), ("B", "U"), ("a", "A"), ("b", "B")],
                        "const A B b a",
                        "b",
                    ),
                    (
                        &[("A", "U"), ("P", "A → U"), ("Q", "Π a : A. (P a → U)"), ("g", "Π a : A. Pi (P a) (Q a)"), ("f", "Pi A P"), ("a", "A")],
                        "subst A P Q g f a",
                        "g a (f a)",
                    ),
                ],
            },
            TypeInit {
                ctor: ("Sigma", "Π A : U. ((A → U) → U)"),
                intro: &[(
                    "Sigma_intro",
                    "Π A : U. Π P : A → U. Π a : A. (P a → Sigma A P)",
                )],
                elim: &[
                    ("Sigma_fst", "Π A : U. Π P : A → U. (Sigma A P → A)"),
                    (
                        "Sigma_snd",
                        "Π A : U. Π P : A → U. Π p : Sigma A P. P (Sigma_fst A P p)",
                    ),
                ],
                red: &[
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
                ],
            },
        ],
        &[
            DefInit {
                sym: ("pair", "Π A B : U. (A → B → (A × B))"),
                red: &[(
                    &[("A", "U"), ("B", "U")],
                    "pair A B",
                    "Sigma_intro A (λ a : A. B)",
                )],
            },
            DefInit {
                sym: ("pair_fst", "Π A B : U. ((A × B) → A)"),
                red: &[(
                    &[("A", "U"), ("B", "U")],
                    "pair_fst A B",
                    "Sigma_fst A (λ a : A. B)",
                )],
            },
            DefInit {
                sym: ("pair_snd", "Π A B : U. ((A × B) → B)"),
                red: &[(
                    &[("A", "U"), ("B", "U")],
                    "pair_snd A B",
                    "Sigma_snd A (λ a : A. B)",
                )],
            },
        ],
        |ctx| Box::new(MLTTLambdaHandler::new(ctx)),
    )
    .unwrap()
}

struct MLTTLambdaHandler {
    u_idx: VarIndex,
    pi_idx: VarIndex,
    sigma_idx: VarIndex,
    id_idx: VarIndex,
    const_idx: VarIndex,
    subst_idx: VarIndex,
}

impl MLTTLambdaHandler {
    fn new(ctx: &[Param]) -> Self {
        MLTTLambdaHandler {
            u_idx: ctx.get_var_index("U", 0).unwrap(),
            pi_idx: ctx.get_var_index("Pi", 0).unwrap(),
            sigma_idx: ctx.get_var_index("Sigma", 0).unwrap(),
            id_idx: ctx.get_var_index("id", 0).unwrap(),
            const_idx: ctx.get_var_index("const", 0).unwrap(),
            subst_idx: ctx.get_var_index("subst", 0).unwrap(),
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
        _: MinimalContext,
    ) -> Result<Expr, String> {
        let idx = match kind {
            DependentTypeCtorKind::Pi => self.pi_idx,
            DependentTypeCtorKind::Sigma => self.sigma_idx,
        };
        Ok(Expr::multi_app(Expr::var(idx), smallvec![domain, prop]))
    }

    fn get_id_cmb(&self, domain: Expr, _: MinimalContext) -> Result<Expr, String> {
        Ok(Expr::app(Expr::var(self.id_idx), domain))
    }

    fn get_const_cmb(
        &self,
        domain: Expr,
        codomain: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.const_idx),
            smallvec![domain, codomain],
        ))
    }

    fn get_subst_cmb(
        &self,
        domain: Expr,
        prop1: Expr,
        prop2: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.subst_idx),
            smallvec![domain, prop1, prop2],
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basics() {
        let mltt = get_mltt();

        let pi = mltt.get_constant("Pi").unwrap();
        assert_eq!(mltt.print_expr(&pi.type_expr), "Π A : U. ((A → U) → U)");

        let id_ctor = mltt.parse_expr("λ A : U. A").unwrap();
        assert_eq!(mltt.print_expr(&id_ctor), "λ A : U. A");
        let id_ctor_type = mltt.get_expr_type(&id_ctor).unwrap();
        assert_eq!(mltt.print_expr(&id_ctor_type), "U → U");

        let const_ctor = mltt.parse_expr("λ A B : U. A").unwrap();
        assert_eq!(mltt.print_expr(&const_ctor), "λ A : U. λ B : U. A");
        let const_ctor_type = mltt.get_expr_type(&const_ctor).unwrap();
        assert_eq!(mltt.print_expr(&const_ctor_type), "U → U → U");

        let const_ctor_occ = mltt.parse_expr("λ A A : U. A@1").unwrap();
        assert_eq!(mltt.print_expr(&const_ctor_occ), "λ A : U. λ A : U. A@1");
        assert_eq!(const_ctor_occ, const_ctor);

        let const_id_ctor_occ = mltt.parse_expr("λ A A : U. A").unwrap();
        assert_eq!(mltt.print_expr(&const_id_ctor_occ), "λ A : U. λ A : U. A");
        assert_ne!(const_id_ctor_occ, const_ctor);

        let app_u = mltt.parse_expr("λ F : U → U. F U").unwrap();
        let app_u_type = mltt.get_expr_type(&app_u).unwrap();
        assert_eq!(mltt.print_expr(&app_u_type), "(U → U) → U");

        let id_fun = mltt.parse_expr("λ A : U. λ a : A. a").unwrap();
        let id_fun_type = mltt.get_expr_type(&id_fun).unwrap();
        assert_eq!(mltt.print_expr(&id_fun_type), "Π A : U. (A → A)");

        let inner_const_fun = mltt.parse_expr("λ A : U. λ a b : A. a").unwrap();
        assert_eq!(
            mltt.print_expr(&inner_const_fun),
            "λ A : U. λ a : A. λ b : A. a"
        );
        let inner_const_fun_type = mltt.get_expr_type(&inner_const_fun).unwrap();
        assert_eq!(
            mltt.print_expr(&inner_const_fun_type),
            "Π A : U. (A → A → A)"
        );

        let pair_fun = mltt
            .parse_expr("λ A B : U. λ a : A. λ b : B. pair A B a b")
            .unwrap();
        let pair_fun_type = mltt.get_expr_type(&pair_fun).unwrap();
        assert_eq!(
            mltt.print_expr(&pair_fun_type),
            "Π A : U. Π B : U. (A → B → (A × B))"
        );

        let mut pair_fst_fun = mltt
            .parse_expr("λ A B : U. λ a : A. λ b : B. pair_fst A B (pair A B a b)")
            .unwrap();
        let pair_fst_fun_type = mltt.get_expr_type(&pair_fst_fun).unwrap();
        assert_eq!(
            mltt.print_expr(&pair_fst_fun_type),
            "Π A : U. Π B : U. (A → B → A)"
        );
        let pair_fst_fun_reduced = mltt.reduce_expr(&mut pair_fst_fun, false);
        assert!(pair_fst_fun_reduced);
        assert_eq!(
            mltt.print_expr(&pair_fst_fun),
            "λ A : U. λ B : U. λ a : A. λ b : B. a"
        );

        let mut pi_type_red = pi.type_expr.clone();
        let pi_type_reduced = mltt.reduce_expr(&mut pi_type_red, true);
        //assert!(pi_type_reduced);
        //assert_eq!(mltt.print_expr(&pi_type_red), "todo");
    }

    #[test]
    fn test_type_errors() {
        let mltt = get_mltt();

        let non_fun_app = mltt.parse_expr("λ A : U. A A").unwrap();
        assert!(mltt.get_expr_type(&non_fun_app).is_err());

        let app_mismatch = mltt.parse_expr("λ F : U → U. F F").unwrap();
        assert!(mltt.get_expr_type(&app_mismatch).is_err());
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
    // TODO: test that specific known terms with multiple reductions are confluent
}
