use smallvec::smallvec;

use crate::{
    generic::context::*,
    metalogic::{expr::*, helpers::*, metalogic::*},
};

pub fn get_mltt() -> MetaLogic {
    MetaLogic::construct_semantically(
        &[
            TypeInit {
                ctor: DefInit {
                    sym: ("U", "U"),
                    red: &[]
                },
                defs: &[],
            },
            TypeInit {
                ctor: DefInit {
                    sym: ("Fun", "U → U → U"),
                    red: &[],
                },
                defs: &[
                    DefInit {
                        sym: ("id", "Π A : U. (A → A)"),
                        red: &[(
                            &[("A", "U"), ("a", "A")],
                            "id A a",
                            "a",
                        )],
                    },
                    DefInit {
                        sym: ("const", "Π A B : U. (B → (A → B))"),
                        red: &[(
                            &[("A", "U"), ("B", "U"), ("a", "A"), ("b", "B")],
                            "const A B b a",
                            "b",
                        )],
                    },
                    DefInit {
                        sym: ("subst", "Π A B C : U. ((A → B → C) → (A → B) → (A → C))"),
                        red: &[(
                            &[("A", "U"), ("B", "U"), ("C", "U"), ("g", "A → B → C"), ("f", "A → B"), ("a", "A")],
                            "subst A B C g f a",
                            "g a (f a)",
                        )],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: ("Pi", "Π A : U. ((A → U) → U)"),
                    red: &[(
                        &[("A", "U"), ("B", "U")],
                        "Pi A (const A U B)",
                        "A → B",
                    )],
                },
                defs: &[
                    DefInit {
                        sym: ("subst_01", "Π A B : U. Π Q : A → U. ((Π a : A. (B → Q a)) → (A → B) → Pi A Q)"),
                        red: &[
                            (
                                &[("A", "U"), ("B", "U"), ("Q", "A → U"), ("g", "Π a : A. (B → Q a)"), ("f", "A → B"), ("a", "A")],
                                "subst_01 A B Q g f a",
                                "g a (f a)",
                            ),
                            (
                                &[("A", "U"), ("B", "U"), ("C", "U")],
                                "subst_01 A B (const A U C)",
                                "subst A B C",
                            ),
                        ],
                    },
                    DefInit {
                        sym: ("subst_02", "Π A B : U. Π Q : (A → B → U). ((Π a : A. Pi B (Q a)) → (Π f : A → B. Π a : A. Q a (f a)))"),
                        red: &[
                            (
                                &[("A", "U"), ("B", "U"), ("Q", "A → B → U"), ("g", "Π a : A. Pi B (Q a)"), ("f", "A → B"), ("a", "A")],
                                "subst_02 A B Q g f a",
                                "g a (f a)",
                            ),
                            (
                                &[("A", "U"), ("B", "U"), ("Q", "A → U")],
                                "subst_02 A B (subst A U (B → U) (const A (U → B → U) (const B U)) Q)",
                                "subst_01 A B Q",
                            ),
                        ],
                    },
                    DefInit {
                        sym: ("subst_10", "Π A : U. Π P : A → U. Π C : U. ((Π a : A. (P a → C)) → Pi A P → A → C)"),
                        red: &[
                            (
                                &[("A", "U"), ("P", "A → U"), ("C", "U"), ("g", "Π a : A. (P a → C)"), ("f", "Pi A P"), ("a", "A")],
                                "subst_10 A P C g f a",
                                "g a (f a)",
                            ),
                            (
                                &[("A", "U"), ("B", "U")],
                                "subst_10 A (const A U B)",
                                "subst A B",
                            ),
                        ],
                    },
                    DefInit {
                        sym: ("subst_11", "Π A : U. Π P Q : A → U. ((Π a : A. (P a → Q a)) → Pi A P → Pi A Q)"),
                        red: &[
                            (
                                &[("A", "U"), ("P", "A → U"), ("Q", "A → U"), ("g", "Π a : A. (P a → Q a)"), ("f", "Pi A P"), ("a", "A")],
                                "subst_11 A P Q g f a",
                                "g a (f a)",
                            ),
                            (
                                &[("A", "U"), ("P", "A → U"), ("C", "U")],
                                "subst_11 A P (const A U C)",
                                "subst_10 A P C",
                            ),
                            (
                                &[("A", "U"), ("B", "U")],
                                "subst_11 A (const A U B)",
                                "subst_01 A B",
                            )
                        ],
                    },
                    DefInit {
                        sym: ("subst_12", "Π A : U. Π P : A → U. Π Q : (Π a : A. (P a → U)). ((Π a : A. Pi (P a) (Q a)) → (Π f : Pi A P. Π a : A. Q a (f a)))"),
                        red: &[
                            (
                                &[("A", "U"), ("P", "A → U"), ("Q", "Π a : A. (P a → U)"), ("g", "Π a : A. Pi (P a) (Q a)"), ("f", "Pi A P"), ("a", "A")],
                                "subst_12 A P Q g f a",
                                "g a (f a)",
                            ),
                            (
                                &[("A", "U"), ("P", "A → U"), ("Q", "A → U")],
                                "subst_12 A P (subst_01 A U (subst A U U (subst A U (U → U) (const A (U → U → U) Fun) P) (const A U U)) (subst_02 A U (subst A (U → U) (U → U) (const A ((U → U) → U → U) (subst U U U Fun)) (subst A U (U → U) (const A (U → U → U) Fun) P)) (subst_02 A U (const A (U → U) (subst U (U → U) U (const U ((U → U) → U) (Pi U)) (subst U (U → U) (U → U) (const U ((U → U) → U → U) (subst U U U Fun)) Fun))) (const A (Pi U (subst U (U → U) U (const U ((U → U) → U) (Pi U)) (subst U (U → U) (U → U) (const U ((U → U) → U → U) (subst U U U Fun)) Fun))) const) P) (const A U U)) Q)",
                                "subst_11 A P Q",
                            ),
                            (
                                &[("A", "U"), ("B", "U")],
                                "subst_12 A (const A U B)",
                                "subst_02 A B",
                            ),
                        ],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: ("Prod", "U → U → U"),
                    red: &[],
                },
                defs: &[
                    DefInit {
                        sym: ("Prod_intro", "Π A B : U. (A → B → (A × B))"),
                        red: &[],
                    },
                    DefInit {
                        sym: ("Prod_fst", "Π A B : U. ((A × B) → A)"),
                        red: &[(
                            &[("A", "U"), ("B", "U"), ("a", "A"), ("b", "B")],
                            "Prod_fst A B (Prod_intro A B a b)",
                            "a",
                        )],
                    },
                    DefInit {
                        sym: ("Prod_snd", "Π A B : U. ((A × B) → B))"),
                        red: &[(
                            &[("A", "U"), ("B", "U"), ("a", "A"), ("b", "B")],
                            "Prod_snd A B (Prod_intro A B a b)",
                            "b",
                        )],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: ("Sigma", "Π A : U. ((A → U) → U)"),
                    red: &[(
                        &[("A", "U"), ("B", "U")],
                        "Sigma A (const A U B)",
                        "A × B",
                    )],
                },
                defs: &[
                    DefInit {
                        sym: ("Sigma_intro", "Π A : U. Π P : A → U. Π a : A. (P a → Sigma A P)"),
                        red: &[(
                            &[("A", "U"), ("B", "U")],
                            "Sigma_intro A (const A U B)",
                            "Prod_intro A B",
                        )],
                    },
                    DefInit {
                        sym: ("Sigma_fst", "Π A : U. Π P : A → U. (Sigma A P → A)"),
                        red: &[
                            (
                                &[("A", "U"), ("P", "A → U"), ("a", "A"), ("b", "P a")],
                                "Sigma_fst A P (Sigma_intro A P a b)",
                                "a",
                            ),
                            (
                                &[("A", "U"), ("B", "U")],
                                "Sigma_fst A (const A U B)",
                                "Prod_fst A B",
                            ),
                        ],
                    },
                    DefInit {
                        sym: ("Sigma_snd", "Π A : U. Π P : A → U. Π p : Sigma A P. P (Sigma_fst A P p)"),
                        red: &[
                            (
                                &[("A", "U"), ("P", "A → U"), ("a", "A"), ("b", "P a")],
                                "Sigma_snd A P (Sigma_intro A P a b)",
                                "b",
                            ),
                            (
                                &[("A", "U"), ("B", "U")],
                                "Sigma_snd A (const A U B)",
                                "Prod_snd A B",
                            ),
                        ],
                    },
                ],
            },
        ],
        |ctx| Box::new(MLTTLambdaHandler::new(ctx)),
    )
    .unwrap()
}

struct MLTTLambdaHandler {
    u_idx: VarIndex,
    fun_idx: VarIndex,
    pi_idx: VarIndex,
    prod_idx: VarIndex,
    sigma_idx: VarIndex,
    id_idx: VarIndex,
    const_idx: VarIndex,
    subst_idx: VarIndex,
    subst_01_idx: VarIndex,
    subst_02_idx: VarIndex,
    subst_10_idx: VarIndex,
    subst_11_idx: VarIndex,
    subst_12_idx: VarIndex,
}

impl MLTTLambdaHandler {
    fn new(ctx: &[Param]) -> Self {
        MLTTLambdaHandler {
            u_idx: ctx.get_var_index("U", 0).unwrap(),
            fun_idx: ctx.get_var_index("Fun", 0).unwrap(),
            pi_idx: ctx.get_var_index("Pi", 0).unwrap(),
            prod_idx: ctx.get_var_index("Prod", 0).unwrap(),
            sigma_idx: ctx.get_var_index("Sigma", 0).unwrap(),
            id_idx: ctx.get_var_index("id", 0).unwrap(),
            const_idx: ctx.get_var_index("const", 0).unwrap(),
            subst_idx: ctx.get_var_index("subst", 0).unwrap(),
            subst_01_idx: ctx.get_var_index("subst_01", 0).unwrap(),
            subst_02_idx: ctx.get_var_index("subst_02", 0).unwrap(),
            subst_10_idx: ctx.get_var_index("subst_10", 0).unwrap(),
            subst_11_idx: ctx.get_var_index("subst_11", 0).unwrap(),
            subst_12_idx: ctx.get_var_index("subst_12", 0).unwrap(),
        }
    }
}

impl LambdaHandler for MLTTLambdaHandler {
    fn get_universe_type(&self) -> Result<Expr, String> {
        Ok(Expr::var(self.u_idx))
    }

    fn get_indep_type(
        &self,
        domain: Expr,
        codomain: Expr,
        kind: DependentTypeCtorKind,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        let idx = match kind {
            DependentTypeCtorKind::Pi => self.fun_idx,
            DependentTypeCtorKind::Sigma => self.prod_idx,
        };
        Ok(Expr::multi_app(Expr::var(idx), smallvec![domain, codomain]))
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

    fn get_indep_subst_cmb(
        &self,
        domain: Expr,
        codomain1: Expr,
        codomain2: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.subst_idx),
            smallvec![domain, codomain1, codomain2],
        ))
    }

    fn get_dep01_subst_cmb(
        &self,
        domain: Expr,
        codomain1: Expr,
        prop2: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.subst_01_idx),
            smallvec![domain, codomain1, prop2],
        ))
    }

    fn get_dep02_subst_cmb(
        &self,
        domain: Expr,
        codomain1: Expr,
        rel2: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.subst_02_idx),
            smallvec![domain, codomain1, rel2],
        ))
    }

    fn get_dep10_subst_cmb(
        &self,
        domain: Expr,
        prop1: Expr,
        codomain2: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.subst_10_idx),
            smallvec![domain, prop1, codomain2],
        ))
    }

    fn get_dep11_subst_cmb(
        &self,
        domain: Expr,
        prop1: Expr,
        prop2: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.subst_11_idx),
            smallvec![domain, prop1, prop2],
        ))
    }

    fn get_dep12_subst_cmb(
        &self,
        domain: Expr,
        prop1: Expr,
        rel2: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.subst_12_idx),
            smallvec![domain, prop1, rel2],
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basics() -> Result<(), String> {
        let mltt = get_mltt();

        let univ = mltt.parse_expr("U")?;

        let pi = mltt.get_constant("Pi").unwrap();
        assert_eq!(mltt.print_expr(&pi.type_expr), "Π A : U. ((A → U) → U)");

        let id_cmb = mltt.get_constant("id").unwrap();
        assert_eq!(mltt.print_expr(&id_cmb.type_expr), "Π A : U. (A → A)");

        let const_cmb = mltt.get_constant("const").unwrap();
        assert_eq!(
            mltt.print_expr(&const_cmb.type_expr),
            "Π A : U. Π B : U. (B → A → B)"
        );

        let subst_cmb = mltt.get_constant("subst").unwrap();
        assert_eq!(
            mltt.print_expr(&subst_cmb.type_expr),
            "Π A : U. Π B : U. Π C : U. ((A → B → C) → (A → B) → A → C)"
        );

        let subst_11_cmb = mltt.get_constant("subst_11").unwrap();
        assert_eq!(
            mltt.print_expr(&subst_11_cmb.type_expr),
            "Π A : U. Π P : A → U. Π Q : A → U. ((Π a : A. (P a → Q a)) → Pi A P → Pi A Q)"
        );

        let subst_12_cmb = mltt.get_constant("subst_12").unwrap();
        assert_eq!(
            mltt.print_expr(&subst_12_cmb.type_expr),
            "Π A : U. Π P : A → U. Π Q : (Π a : A. (P a → U)). ((Π a : A. Pi (P a) (Q a)) → (Π f : Pi A P. Π a : A. Q a (f a)))"
        );

        let mut id_ctor = mltt.parse_expr("λ A : U. A")?;
        assert_eq!(mltt.print_expr(&id_ctor), "λ A : U. A");
        let id_ctor_type = mltt.get_expr_type(&id_ctor)?;
        assert_eq!(mltt.print_expr(&id_ctor_type), "U → U");

        let mut const_ctor = mltt.parse_expr("λ A B : U. A")?;
        assert_eq!(mltt.print_expr(&const_ctor), "λ A : U. λ B : U. A");
        let const_ctor_type = mltt.get_expr_type(&const_ctor)?;
        assert_eq!(mltt.print_expr(&const_ctor_type), "U → U → U");

        let const_ctor_occ = mltt.parse_expr("λ A A : U. A@1")?;
        assert_eq!(mltt.print_expr(&const_ctor_occ), "λ A : U. λ A : U. A@1");
        assert_eq!(const_ctor_occ, const_ctor);

        let const_id_ctor_occ = mltt.parse_expr("λ A A : U. A")?;
        assert_eq!(mltt.print_expr(&const_id_ctor_occ), "λ A : U. λ A : U. A");
        assert_ne!(const_id_ctor_occ, const_ctor);

        let mut app_u = mltt.parse_expr("λ F : U → U. F U")?;
        let app_u_type = mltt.get_expr_type(&app_u)?;
        assert_eq!(mltt.print_expr(&app_u_type), "(U → U) → U");

        let mut id_fun = mltt.parse_expr("λ A : U. λ a : A. a")?;
        let id_fun_type = mltt.get_expr_type(&id_fun)?;
        assert_eq!(mltt.print_expr(&id_fun_type), "Π A : U. (A → A)");

        let inner_const_fun = mltt.parse_expr("λ A : U. λ a b : A. a")?;
        assert_eq!(
            mltt.print_expr(&inner_const_fun),
            "λ A : U. λ a : A. λ b : A. a"
        );
        let inner_const_fun_type = mltt.get_expr_type(&inner_const_fun)?;
        assert_eq!(
            mltt.print_expr(&inner_const_fun_type),
            "Π A : U. (A → A → A)"
        );

        let pair_fun = mltt.parse_expr("λ A B : U. λ a : A. λ b : B. Prod_intro A B a b")?;
        let pair_fun_type = mltt.get_expr_type(&pair_fun)?;
        assert_eq!(
            mltt.print_expr(&pair_fun_type),
            "Π A : U. Π B : U. (A → B → (A × B))"
        );

        let mut pair_fst_fun =
            mltt.parse_expr("λ A B : U. λ a : A. λ b : B. Prod_fst A B (Prod_intro A B a b)")?;
        let pair_fst_fun_type = mltt.get_expr_type(&pair_fst_fun)?;
        assert_eq!(
            mltt.print_expr(&pair_fst_fun_type),
            "Π A : U. Π B : U. (A → B → A)"
        );
        let pair_fst_fun_reduced = mltt.reduce_expr(&mut pair_fst_fun, -1)?;
        assert!(pair_fst_fun_reduced);
        assert_eq!(
            mltt.print_expr(&pair_fst_fun),
            "λ A : U. λ B : U. λ a : A. λ b : B. a"
        );

        mltt.convert_expr_to_combinators(&mut id_ctor, -1)?;
        assert_eq!(mltt.print_expr(&id_ctor), "id U");

        mltt.convert_expr_to_combinators(&mut const_ctor, -1)?;
        assert_eq!(mltt.print_expr(&const_ctor), "const U U");

        mltt.convert_expr_to_combinators(&mut app_u, -1)?;
        assert_eq!(
            mltt.print_expr(&app_u),
            "subst (U → U) U U (id (U → U)) (const (U → U) U U)"
        );
        let app_u_cmb_type = mltt.get_expr_type(&app_u)?;
        assert!(app_u_cmb_type.is_defeq(&app_u_type, &mltt.get_root_context())?);

        mltt.convert_expr_to_combinators(&mut id_fun, -1)?;
        assert_eq!(mltt.print_expr(&id_fun), "id");

        let mut pi_type = pi.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut pi_type, -1)?;
        assert_eq!(
            mltt.print_expr(&pi_type),
            "Pi U (subst U U U (subst U U (U → U) (const U (U → U → U) Fun) (subst U U U Fun (const U U U))) (const U U U))"
        );

        let mut id_cmb_type = id_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut id_cmb_type, -1)?;
        assert_eq!(
            mltt.print_expr(&id_cmb_type),
            "Pi U (subst U U U Fun (id U))"
        );
        assert_eq!(mltt.get_expr_type(&id_cmb_type)?, univ);

        let mut const_cmb_type = const_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut const_cmb_type, -1)?;
        assert_eq!(
            mltt.print_expr(&const_cmb_type),
            "Pi U (subst U (U → U) U (const U ((U → U) → U) (Pi U)) (subst U (U → U) (U → U) (const U ((U → U) → U → U) (subst U U U Fun)) Fun))"
        );
        assert_eq!(mltt.get_expr_type(&const_cmb_type)?, univ);

        let mut subst_cmb_type = subst_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut subst_cmb_type, -1)?;
        assert_eq!(
            mltt.print_expr(&subst_cmb_type),
            "Pi U (subst U (U → U) U (const U ((U → U) → U) (Pi U)) (subst U (U → U → U) (U → U) (const U ((U → U → U) → U → U) (subst U (U → U) U (const U ((U → U) → U) (Pi U)))) (subst U (U → U → U) (U → U → U) (subst U (U → (U → U) → U → U) ((U → U → U) → U → U → U) (const U ((U → (U → U) → U → U) → (U → U → U) → U → U → U) (subst U (U → U) (U → U))) (subst U (U → U → U → U) (U → (U → U) → U → U) (const U ((U → U → U → U) → U → (U → U) → U → U) (subst U (U → U → U) ((U → U) → U → U) (const U ((U → U → U) → (U → U) → U → U) (subst U U U)))) (subst U (U → U → U) (U → U → U → U) (const U ((U → U → U) → U → U → U → U) (subst U (U → U) (U → U → U) (const U ((U → U) → U → U → U) (subst U U (U → U) (const U (U → U → U) Fun))))) (subst U (U → U → U) (U → U → U) (subst U (U → (U → U) → U → U) ((U → U → U) → U → U → U) (const U ((U → (U → U) → U → U) → (U → U → U) → U → U → U) (subst U (U → U) (U → U))) (subst U ((U → U) → U → U) (U → (U → U) → U → U) (const U (((U → U) → U → U) → U → (U → U) → U → U) (const U ((U → U) → U → U))) (subst U (U → U → U) ((U → U) → U → U) (const U ((U → U → U) → (U → U) → U → U) (subst U U U)) (subst U (U → U) (U → U → U) (const U ((U → U) → U → U → U) (const U (U → U))) Fun)))) (const U (U → U → U) Fun))))) (subst U (U → U → U) (U → U → U) (subst U (U → (U → U) → U → U) ((U → U → U) → U → U → U) (const U ((U → (U → U) → U → U) → (U → U → U) → U → U → U) (subst U (U → U) (U → U))) (subst U (U → U → U → U) (U → (U → U) → U → U) (const U ((U → U → U → U) → U → (U → U) → U → U) (subst U (U → U → U) ((U → U) → U → U) (const U ((U → U → U) → (U → U) → U → U) (subst U U U)))) (subst U (U → U → U) (U → U → U → U) (const U ((U → U → U) → U → U → U → U) (subst U (U → U) (U → U → U) (const U ((U → U) → U → U → U) (const U (U → U))))) (subst U (U → U) (U → U → U) (const U ((U → U) → U → U → U) (subst U U (U → U) (const U (U → U → U) Fun))) Fun)))) (subst U (U → U) (U → U → U) (const U ((U → U) → U → U → U) (const U (U → U))) Fun)))))"
        );
        assert_eq!(mltt.get_expr_type(&subst_cmb_type)?, univ);

        let mut subst_11_cmb_type = subst_11_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut subst_11_cmb_type, 2)?;
        assert_eq!(
            mltt.print_expr(&subst_11_cmb_type),
            "Pi U (subst_10 U (λ A : U. ((A → U) → U)) U (λ A : U. Pi (A → U)) (λ A : U. λ P : A → U. Π Q : A → U. ((Π a : A. (P a → Q a)) → Pi A P → Pi A Q)))"
        );
        assert_eq!(mltt.get_expr_type(&subst_11_cmb_type)?, univ);

        let mut subst_12_cmb_type = subst_12_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut subst_12_cmb_type, 2)?;
        assert_eq!(
            mltt.print_expr(&subst_12_cmb_type),
            "Pi U (subst_10 U (λ A : U. ((A → U) → U)) U (λ A : U. Pi (A → U)) (λ A : U. λ P : A → U. Π Q : (Π a : A. (P a → U)). ((Π a : A. Pi (P a) (Q a)) → (Π f : Pi A P. Π a : A. Q a (f a)))))"
        );
        assert_eq!(mltt.get_expr_type(&subst_12_cmb_type)?, univ);

        Ok(())
    }

    #[test]
    fn test_type_errors() -> Result<(), String> {
        let mltt = get_mltt();

        let non_fun_app = mltt.parse_expr("λ A : U. A A")?;
        assert!(mltt.get_expr_type(&non_fun_app).is_err());

        let app_mismatch = mltt.parse_expr("λ F : U → U. F F")?;
        assert!(mltt.get_expr_type(&app_mismatch).is_err());

        Ok(())
    }

    #[test]
    fn test_type_of_types() -> Result<(), Vec<String>> {
        let mltt = get_mltt();
        mltt.check_type_of_types()
    }

    #[test]
    fn test_reduction_rule_types() -> Result<(), Vec<String>> {
        let mltt = get_mltt();
        mltt.check_reduction_rule_types()
    }

    // TODO: test that all declared types reduce uniquely (are confluent)
    // TODO: test that specific known terms with multiple reductions are confluent
}
