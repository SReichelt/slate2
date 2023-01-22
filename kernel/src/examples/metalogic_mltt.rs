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
                    sym: "U : U",
                    red: &[]
                },
                defs: &[],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Pi : Π A : U. ((A → U) → U)",
                    red: &[],
                },
                defs: &[
                    DefInit {
                        sym: "id : Π A : U. (A → A)",
                        red: &["∀ A : U. ∀ a : A. id A a :≡ a"],
                    },
                    DefInit {
                        sym: "const : Π A B : U. (B → (A → B))",
                        red: &["∀ A B : U. ∀ a : A. ∀ b : B. const A B b a :≡ b"],
                    },
                    DefInit {
                        sym: "subst : Π A : U. Π P : A → U. Π Q : (Π a : A. (P a → U)). ((Π a : A. Pi (P a) (Q a)) → (Π f : Pi A P. Π a : A. Q a (f a)))",
                        red: &["∀ A : U. ∀ P : A → U. ∀ Q : (Π a : A. (P a → U)). ∀ g : (Π a : A. Pi (P a) (Q a)). ∀ f : Pi A P. ∀ a : A. subst A P Q g f a :≡ g a (f a)"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Sigma : Π A : U. ((A → U) → U)",
                    red: &[],
                },
                defs: &[
                    DefInit {
                        sym: "Sigma_intro : Π A : U. Π P : A → U. Π a : A. (P a → Sigma A P)",
                        red: &[],
                    },
                    DefInit {
                        sym: "Sigma_fst : Π A : U. Π P : A → U. (Sigma A P → A)",
                        red: &["∀ A : U. ∀ P : A → U. ∀ a : A. ∀ b : P a. Sigma_fst A P (Sigma_intro A P a b) :≡ a"],
                    },
                    DefInit {
                        sym: "Sigma_snd : Π A : U. Π P : A → U. Π p : Sigma A P. P (Sigma_fst A P p)",
                        red: &["∀ A : U. ∀ P : A → U. ∀ a : A. ∀ b : P a. Sigma_snd A P (Sigma_intro A P a b) :≡ b"],
                    },
                    DefInit {
                        sym: "pair_intro : Π A B : U. (A → B → (A × B))",
                        red: &["pair_intro :≡ λ A B : U. Sigma_intro A (λ _ : A. B)"],
                    },
                    DefInit {
                        sym: "pair_fst : Π A B : U. ((A × B) → A)",
                        red: &["pair_fst :≡ λ A B : U. Sigma_fst A (λ _ : A. B)"],
                    },
                    DefInit {
                        sym: "pair_snd : Π A B : U. ((A × B) → B)",
                        red: &["pair_snd :≡ λ A B : U. Sigma_snd A (λ _ : A. B)"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Eq : Π A : U. (A → A → U)",
                    red: &[
                        "Eq U :≡ λ A B : U. ((A → B) × (B → A))", // TODO: not the real thing yet
                        "∀ A : U. ∀ P : A → U. Eq (Pi A P) :≡ λ f g : Pi A P. Π a : A. f a ={P a} g a",
                        "∀ A : U. ∀ P : A → U. Eq (Sigma A P) :≡ λ p q : Sigma A P. Σ e_fst : Sigma_fst A P p ={A} Sigma_fst A P q. Sigma_snd A P p ={P (Sigma_fst A P p)}[ap A U P (Sigma_fst A P p) (Sigma_fst A P q) e_fst]{P (Sigma_fst A P q)} Sigma_snd A P q",
                    ],
                },
                defs: &[
                    DefInit {
                        sym: "refl : Π A : U. Π a : A. a = a",
                        red: &[
                            "refl U :≡ λ A : U. pair_intro (A → A) (A → A) (λ a : A. a) (λ a : A. a)",
                            "∀ A : U. ∀ P : A → U. refl (Pi A P) :≡ λ f : Pi A P. λ a : A. refl (P a) (f a)",
                            "∀ A : U. ∀ P : A → U. refl (Sigma A P) :≡ λ p : Sigma A P. Sigma_intro (Sigma_fst A P p ={A} Sigma_fst A P p) (λ e_fst : Sigma_fst A P p ={A} Sigma_fst A P p. Sigma_snd A P p ={P (Sigma_fst A P p)}[ap A U P (Sigma_fst A P p) (Sigma_fst A P p) e_fst]{P (Sigma_fst A P p)} Sigma_snd A P p) (refl A (Sigma_fst A P p)) (refl (P (Sigma_fst A P p)) (Sigma_snd A P p))",
                        ],
                    },
                    // TODO: implement these for different equalities
                    DefInit {
                        sym: "symm : Π A : U. Π a b : A. (a = b → b = a)",
                        red: &[
                            "∀ A : U. ∀ a : A. symm A a a (refl A a) :≡ refl A a",
                            "symm U :≡ λ A B : U. λ e : A = B. pair_intro (B → A) (A → B) (inv A B e) (to A B e)",
                            "∀ A : U. ∀ P : A → U. symm (Pi A P) :≡ λ f g : Pi A P. λ e : f = g. λ a : A. symm (P a) (f a) (g a) (e a)",
                            // TODO
                            //"∀ A : U. ∀ P : A → U. symm (Sigma A P) :≡ λ p q : Sigma A P. λ e : p = q. Sigma_intro _ _ (symm _ _ _ (Sigma_fst _ _ e)) (symmd ... (Sigma_snd _ _ e))",
                        ],
                    },
                    DefInit {
                        sym: "trans : Π A : U. Π a b c : A. (a = b → b = c → a = c)",
                        red: &[
                            "∀ A : U. ∀ a b : A. ∀ e : a = b. trans A a a b (refl A a) e :≡ e",
                            "∀ A : U. ∀ a b : A. ∀ e : a = b. trans A a b b e (refl A b) :≡ e",
                            "trans U :≡ λ A B C : U. λ e : A = B. λ f : B = C. pair_intro (A → C) (C → A) (λ a : A. to B C f (to A B e a)) (λ c : C. inv A B e (inv B C f c))",
                            "∀ A : U. ∀ P : A → U. trans (Pi A P) :≡ λ f g h : Pi A P. λ efg : f = g. λ egh : g = h. λ a : A. trans (P a) (f a) (g a) (h a) (efg a) (egh a)",
                            // TODO
                        ],
                    },
                    // TODO groupoid laws
                    DefInit {
                        sym: "to : Π A B : U. ((A = B) → A → B)",
                        red: &["to :≡ λ A B : U. pair_fst (A → B) (B → A)"],
                    },
                    DefInit {
                        sym: "inv : Π A B : U. ((A = B) → B → A)",
                        red: &["inv :≡ λ A B : U. pair_snd (A → B) (B → A)"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "DepEq : Π A B : U. ((A = B) → A → B → U)",
                    red: &["DepEq :≡ λ A B : U. λ e : A = B. λ a : A. λ b : B. to A B e a = b"],
                },
                defs: &[
                    // TODO: symm, trans
                ],
            },
        ],
        &[
            DefInit {
                sym: "apd : Π A : U. Π P : A → U. Π f : Pi A P. Π a a' : A. Π e : a = a'. f a ={P a}[ap A U P a a' e]{P a'} f a'",
                red: &[
                    "∀ A : U. ∀ P : A → U. ∀ f : Pi A P. ∀ a : A. apd A P f a a (refl A a) :≡ refl (P a) (f a)",
                    "∀ A : U. apd A (const A U A) (id A) :≡ λ a a' : A. λ e : a = a'. e",
                    "∀ A B : U. ∀ b : B. apd A (const A U B) (const A B b) :≡ λ a a' : A. λ e : a = a'. refl B b",
                    "∀ A B : U. apd B (const B U (A → B)) (const A B) :≡ λ b b' : B. λ e : b = b'. λ a : A. e",
                    // TODO: lots more
                ],
            },
            DefInit {
                sym: "ap : Π A B : U. Π f : A → B. Π a a' : A. (a = a' → f a ={B} f a')",
                red: &["ap :≡ λ A B : U. apd A (λ _ : A. B)"],
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
    eq_idx: VarIndex,
    dep_eq_idx: VarIndex,
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
            eq_idx: ctx.get_var_index("Eq", 0).unwrap(),
            dep_eq_idx: ctx.get_var_index("DepEq", 0).unwrap(),
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
        rel2: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.subst_idx),
            smallvec![domain, prop1, rel2],
        ))
    }

    fn get_indep_eq_type(
        &self,
        domain: Expr,
        left: Expr,
        right: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.eq_idx),
            smallvec![domain, left, right],
        ))
    }

    fn get_dep_eq_type(
        &self,
        left_domain: Expr,
        right_domain: Expr,
        domain_eq: Expr,
        left: Expr,
        right: Expr,
        _: MinimalContext,
    ) -> Result<Expr, String> {
        Ok(Expr::multi_app(
            Expr::var(self.dep_eq_idx),
            smallvec![left_domain, right_domain, domain_eq, left, right],
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

        let pair_fun = mltt.parse_expr("λ A B : U. λ a : A. λ b : B. pair_intro A B a b")?;
        let pair_fun_type = mltt.get_expr_type(&pair_fun)?;
        assert_eq!(
            mltt.print_expr(&pair_fun_type),
            "Π A : U. Π B : U. (A → B → (A × B))"
        );

        let mut pair_fst_fun =
            mltt.parse_expr("λ A B : U. λ a : A. λ b : B. pair_fst A B (pair_intro A B a b)")?;
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
            "subst (Pi U (const U U U)) (const (Pi U (const U U U)) U U) (const (Pi U (const U U U)) (Pi U (const U U U)) (const U U U)) (id (Pi U (const U U U))) (const (Pi U (const U U U)) U U)"
        );
        let app_u_cmb_type = mltt.get_expr_type(&app_u)?;
        assert!(app_u_cmb_type.is_defeq(&app_u_type, &mltt.get_root_context())?);

        mltt.convert_expr_to_combinators(&mut id_fun, -1)?;
        assert_eq!(mltt.print_expr(&id_fun), "id");

        let mut pi_type = pi.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut pi_type, 2)?;
        assert_eq!(
            mltt.print_expr(&pi_type),
            "Pi U (subst U (λ A : U. ((A → U) → U)) (λ A : U. λ _ : (A → U) → U. U) (λ A : U. Pi (A → U)) (λ A : U. λ _ : A → U. U))"
        );

        let mut id_cmb_type = id_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut id_cmb_type, 2)?;
        assert_eq!(
            mltt.print_expr(&id_cmb_type),
            "Pi U (subst U (λ A : U. (A → U)) (λ A : U. λ _ : A → U. U) (λ A : U. Pi A) (λ A : U. λ _ : A. A))"
        );
        assert_eq!(mltt.get_expr_type(&id_cmb_type)?, univ);

        let mut const_cmb_type = const_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut const_cmb_type, 2)?;
        assert_eq!(
            mltt.print_expr(&const_cmb_type),
            "Pi U (subst U (λ A : U. (U → U)) (λ A : U. λ _ : U → U. U) (λ A : U. Pi U) (λ A : U. λ B : U. (B → A → B)))"
        );
        assert_eq!(mltt.get_expr_type(&const_cmb_type)?, univ);

        let mut subst_cmb_type = subst_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut subst_cmb_type, 2)?;
        assert_eq!(
            mltt.print_expr(&subst_cmb_type),
            "Pi U (subst U (λ A : U. ((A → U) → U)) (λ A : U. λ _ : (A → U) → U. U) (λ A : U. Pi (A → U)) (λ A : U. λ P : A → U. Π Q : (Π a : A. (P a → U)). ((Π a : A. Pi (P a) (Q a)) → (Π f : Pi A P. Π a : A. Q a (f a)))))"
        );
        assert_eq!(mltt.get_expr_type(&subst_cmb_type)?, univ);

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
