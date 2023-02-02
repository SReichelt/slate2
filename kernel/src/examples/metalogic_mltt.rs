use anyhow::Result;
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
                    sym: "Empty : U",
                    red: &[]
                },
                defs: &[
                    DefInit {
                        sym: "Empty_elim : Π A : U. Empty → A",
                        red: &[],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Unit : U",
                    red: &[]
                },
                defs: &[
                    DefInit {
                        sym: "unit : Unit",
                        red: &[],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Pi : Π {A : U}. (A → U) → U",
                    red: &[],
                },
                defs: &[
                    DefInit {
                        sym: "id : Π A : U. A → A",
                        red: &["∀ A : U. ∀ a : A. (id A) a :≡ a"],
                    },
                    DefInit {
                        sym: "const : Π A : U. Π {B : U}. B → (A → B)",
                        red: &["∀ A : U. ∀ {B : U}. ∀ b : B. ∀ a : A. (const A b) a :≡ b"],
                    },
                    DefInit {
                        sym: "subst : Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. (Π a : A. Pi (Q a)) → (Π f : Pi P. Π a : A. Q a (f a))",
                        red: &["∀ {A : U}. ∀ {P : A → U}. ∀ {Q : (Π a : A. P a → U)}. ∀ g : (Π a : A. Pi (Q a)). ∀ f : Pi P. ∀ a : A. (subst g f) a :≡ g a (f a)"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Sigma : Π {A : U}. (A → U) → U",
                    red: &[],
                },
                defs: &[
                    DefInit {
                        sym: "Sigma_intro : Π {A : U}. Π P : A → U. Π a : A. P a → Sigma P",
                        red: &[],
                    },
                    DefInit {
                        sym: "Sigma_fst : Π {A : U}. Π {P : A → U}. Sigma P → A",
                        red: &["∀ {A : U}. ∀ {P : A → U}. ∀ a : A. ∀ b : P a. Sigma_fst (Sigma_intro P a b) :≡ a"],
                    },
                    DefInit {
                        sym: "Sigma_snd : Π {A : U}. Π {P : A → U}. Π p : Sigma P. P (Sigma_fst p)",
                        red: &["∀ {A : U}. ∀ {P : A → U}. ∀ a : A. ∀ b : P a. Sigma_snd (Sigma_intro P a b) :≡ b"],
                    },
                    DefInit {
                        sym: "Pair_intro : Π A B : U. A → B → (A × B)",
                        red: &["Pair_intro :≡ λ A B. Sigma_intro {A} (λ _. B)"],
                    },
                    DefInit {
                        sym: "Pair_fst : Π {A B : U}. (A × B) → A",
                        red: &["Pair_fst :≡ λ {A B}. Sigma_fst {A} {λ _. B}"],
                    },
                    DefInit {
                        sym: "Pair_snd : Π {A B : U}. (A × B) → B",
                        red: &["Pair_snd :≡ λ {A B}. Sigma_snd {A} {λ _. B}"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Eq : Π {A : U}. (A → A → U)",
                    red: &[
                        "Eq {U} :≡ λ A B : U. Sigma (SplitEquiv A B)",
                        "Eq {Unit} :≡ λ a b : Unit. Unit",
                        "∀ {A : U}. ∀ P : A → U. Eq {Pi P} :≡ λ f g. Π a : A. f a = g a",
                        "∀ {A : U}. ∀ P : A → U. Eq {Sigma P} :≡ λ p q. Σ e_fst : Sigma_fst p = Sigma_fst q. Sigma_snd p =[ap P e_fst] Sigma_snd q",
                    ],
                },
                defs: &[
                    DefInit {
                        sym: "middle : Π {A B : U}. A = B → U",
                        red: &["middle :≡ λ {A B}. Sigma_fst {U} {SplitEquiv A B}"],
                    },
                    DefInit {
                        sym: "split : Π {A B : U}. Π e : A = B. SplitEquiv A B (middle e)",
                        red: &["split :≡ λ {A B}. Sigma_snd {U} {SplitEquiv A B}"],
                    },
                    DefInit {
                        sym: "refl : Π {A : U}. Π a : A. a = a",
                        red: &[
                            "refl {U} :≡ λ A : U. Sigma_intro (SplitEquiv A A) A (SplitEquiv_refl A)",
                            "refl {Unit} :≡ λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. refl {Pi P} :≡ λ f. λ a : A. refl (f a)",
                            "∀ {A : U}. ∀ P : A → U. refl {Sigma P} :≡ λ p. Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst p. Sigma_snd p =[ap P e_fst] Sigma_snd p) (refl (Sigma_fst p)) (refl (Sigma_snd p))",
                        ],
                    },
                    DefInit {
                        sym: "symm : Π {A : U}. Π {a b : A}. a = b → b = a",
                        red: &[
                            "∀ {A : U}. ∀ a : A. symm (refl a) :≡ refl a",
                            "symm {Unit} :≡ λ {_ _}. λ _. unit",
                            "symm {U} :≡ λ {A B}. λ e. Sigma_intro (SplitEquiv B A) (middle e) (SplitEquiv_symm (split e))",
                            "∀ {A : U}. ∀ P : A → U. symm {Pi P} :≡ λ {f g}. λ e. λ a : A. symm (e a)",
                            "∀ {A : U}. ∀ P : A → U. symm {Sigma P} :≡ λ {p q}. λ e. Sigma_intro (λ e_fst : Sigma_fst q = Sigma_fst p. Sigma_snd q =[ap P e_fst] Sigma_snd p) (symm {_} {Sigma_fst p} {Sigma_fst q} (Sigma_fst e)) (DepEq_symm {_} {_} {ap P {Sigma_fst p} {Sigma_fst q} (Sigma_fst e)} {Sigma_snd p} {Sigma_snd q} (Sigma_snd e))",
                        ],
                    },
                    DefInit {
                        sym: "trans : Π {A : U}. Π {a b c : A}. a = b → b = c → a = c",
                        red: &[
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. trans (refl a) e :≡ e",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. trans e (refl b) :≡ e",
                            "trans {U} :≡ λ {A B C}. λ e f. Sigma_intro (SplitEquiv A C) B (SplitEquiv_trans (split e) (split f))",
                            "trans {Unit} :≡ λ {_ _ _}. λ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. trans {Pi P} :≡ λ {f g h}. λ efg egh. λ a : A. trans (efg a) (egh a)",
                            // TODO
                        ],
                    },
                    // TODO groupoid laws
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "DepEq : Π {A B : U}. A = B → A → B → U",
                    red: &["DepEq :≡ λ {A B}. λ eAB a b. QuasiEquiv_to (SplitEquiv_left (split eAB)) a = QuasiEquiv_to (SplitEquiv_right (split eAB)) b"],
                },
                defs: &[
                    DefInit {
                        sym: "DepEq_refl : Π {A : U}. Π a : A. a =[refl A] a",
                        red: &["DepEq_refl :≡ refl"],
                    },
                    DefInit {
                        sym: "DepEq_symm : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. a =[eAB] b → b =[symm eAB] a",
                        red: &["DepEq_symm :≡ λ {A B eAB a b}. symm {middle eAB} {QuasiEquiv_to (SplitEquiv_left (split eAB)) a} {QuasiEquiv_to (SplitEquiv_right (split eAB)) b}"],
                    },
                    DefInit {
                        sym: "DepEq_trans : Π {A B C : U}. Π {eAB : A = B}. Π {eBC : B = C}. Π {a : A}. Π {b : B}. Π {c : C}. a =[eAB] b → b =[eBC] c → a =[trans eAB eBC] c",
                        // (Note that the middle will be b : B. So we need to shift both equalities to B)
                        red: &[/*"DepEq_trans :≡ λ {A B C eAB eBC a b c}. _"*/],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "QuasiEquiv : U → U → U",
                    red: &["QuasiEquiv :≡ λ A B. ((A → B) × (B → A))"], // TODO
                },
                defs: &[
                    DefInit {
                        sym: "QuasiEquiv_intro : Π {A B : U}. (A → B) → (B → A) → QuasiEquiv A B",
                        red: &["QuasiEquiv_intro :≡ λ {A B}. Pair_intro (A → B) (B → A)"],
                    },
                    DefInit {
                        sym: "QuasiEquiv_to : Π {A B : U}. QuasiEquiv A B → A → B",
                        red: &["QuasiEquiv_to :≡ λ {A B}. Pair_fst {A → B} {B → A}"],
                    },
                    DefInit {
                        sym: "QuasiEquiv_inv : Π {A B : U}. QuasiEquiv A B → B → A",
                        red: &["QuasiEquiv_inv :≡ λ {A B}. Pair_snd {A → B} {B → A}"],
                    },
                    DefInit {
                        sym: "QuasiEquiv_refl : Π A : U. QuasiEquiv A A",
                        red: &["QuasiEquiv_refl :≡ λ A. QuasiEquiv_intro (id A) (id A)"],
                    },
                    DefInit {
                        sym: "QuasiEquiv_symm : Π {A B : U}. QuasiEquiv A B → QuasiEquiv B A",
                        red: &["QuasiEquiv_symm :≡ λ {A B}. λ e. QuasiEquiv_intro (QuasiEquiv_inv e) (QuasiEquiv_to e)"],
                    },
                    DefInit {
                        sym: "QuasiEquiv_trans : Π {A B C : U}. QuasiEquiv A B → QuasiEquiv B C → QuasiEquiv A C",
                        red: &["QuasiEquiv_trans :≡ λ {A B C}. λ e f. QuasiEquiv_intro (λ a. QuasiEquiv_to f (QuasiEquiv_to e a)) (λ c. QuasiEquiv_inv e (QuasiEquiv_inv f c))"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "SplitEquiv : U → U → U → U",
                    red: &["SplitEquiv :≡ λ A B X : U. (QuasiEquiv A X × QuasiEquiv B X)"],
                },
                defs: &[
                    DefInit {
                        sym: "SplitEquiv_intro : Π {A B X : U}. QuasiEquiv A X → QuasiEquiv B X → SplitEquiv A B X",
                        red: &["SplitEquiv_intro :≡ λ {A B X}. Pair_intro (QuasiEquiv A X) (QuasiEquiv B X)"],
                    },
                    DefInit {
                        sym: "SplitEquiv_left : Π {A B X : U}. SplitEquiv A B X → QuasiEquiv A X",
                        red: &["SplitEquiv_left :≡ λ {A B X}. Pair_fst {QuasiEquiv A X} {QuasiEquiv B X}"],
                    },
                    DefInit {
                        sym: "SplitEquiv_right : Π {A B X : U}. SplitEquiv A B X → QuasiEquiv B X",
                        red: &["SplitEquiv_right :≡ λ {A B X}. Pair_snd {QuasiEquiv A X} {QuasiEquiv B X}"],
                    },
                    DefInit {
                        sym: "SplitEquiv_to_QuasiEquiv : Π {A B X : U}. SplitEquiv A B X → QuasiEquiv A B",
                        red: &["SplitEquiv_to_QuasiEquiv :≡ λ {A B X}. λ e. QuasiEquiv_trans (SplitEquiv_left e) (QuasiEquiv_symm (SplitEquiv_right e))"],
                    },
                    DefInit {
                        sym: "SplitEquiv_refl : Π A : U. SplitEquiv A A A",
                        red: &["SplitEquiv_refl :≡ λ A. SplitEquiv_intro (QuasiEquiv_refl A) (QuasiEquiv_refl A)"],
                    },
                    DefInit {
                        sym: "SplitEquiv_symm : Π {A B X : U}. SplitEquiv A B X → SplitEquiv B A X",
                        red: &["SplitEquiv_symm :≡ λ {A B X}. λ e. SplitEquiv_intro (SplitEquiv_right e) (SplitEquiv_left e)"],
                    },
                    DefInit {
                        sym: "SplitEquiv_trans : Π {A B C X Y : U}. SplitEquiv A B X → SplitEquiv B C Y → SplitEquiv A C B",
                        red: &["SplitEquiv_trans :≡ λ {A B C X Y}. λ e f. SplitEquiv_intro (SplitEquiv_to_QuasiEquiv e) (SplitEquiv_to_QuasiEquiv (SplitEquiv_symm f))"],
                    },
                ],
            },
        ],
        &[
            DefInit {
                sym: "apd : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a a' : A}. Π e : a = a'. f a =[ap P e] f a'",
                red: &[
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ a : A. apd f (refl a) :≡ DepEq_refl (f a)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ {a a' : A}. ∀ e : a = a'. apd f (symm e) :≡ DepEq_symm (apd f e)",
                    "∀ {A : U}. apd (id A) :≡ λ {a a'}. λ e. e",
                    "∀ A : U. ∀ {B : U}. ∀ b : B. apd (const A b) :≡ λ {a a'}. λ e. DepEq_refl b",
                    "∀ A B : U. apd (const A {B}) :≡ λ {b b'}. λ e. λ a : A. e",
                    // TODO: lots more
                ],
            },
            DefInit {
                sym: "ap : Π {A B : U}. Π f : A → B. Π {a a' : A}. a = a' → f a = f a'",
                red: &["ap :≡ λ {A B}. apd {A} {λ _. B}"],
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
    fn get_universe_type(&self) -> Result<Expr> {
        Ok(Expr::var(self.u_idx))
    }

    fn get_dep_type(
        &self,
        domain: Expr,
        prop: Expr,
        kind: DependentTypeCtorKind,
        _: MinimalContext,
    ) -> Result<Expr> {
        let idx = match kind {
            DependentTypeCtorKind::Pi => self.pi_idx,
            DependentTypeCtorKind::Sigma => self.sigma_idx,
        };
        let domain_arg = Arg {
            expr: domain,
            implicit: true,
        };
        let prop_arg = Arg {
            expr: prop,
            implicit: false,
        };
        Ok(Expr::multi_app(
            Expr::var(idx),
            smallvec![domain_arg, prop_arg],
        ))
    }

    fn get_id_cmb(&self, domain: Expr, _: MinimalContext) -> Result<Expr> {
        Ok(Expr::explicit_app(Expr::var(self.id_idx), domain))
    }

    fn get_const_cmb(&self, domain: Expr, codomain: Expr, _: MinimalContext) -> Result<Expr> {
        let domain_arg = Arg {
            expr: domain,
            implicit: false,
        };
        let codomain_arg = Arg {
            expr: codomain,
            implicit: true,
        };
        Ok(Expr::multi_app(
            Expr::var(self.const_idx),
            smallvec![domain_arg, codomain_arg],
        ))
    }

    fn get_subst_cmb(
        &self,
        domain: Expr,
        prop1: Expr,
        rel2: Expr,
        _: MinimalContext,
    ) -> Result<Expr> {
        let domain_arg = Arg {
            expr: domain,
            implicit: true,
        };
        let prop1_arg = Arg {
            expr: prop1,
            implicit: true,
        };
        let rel2_arg = Arg {
            expr: rel2,
            implicit: true,
        };
        Ok(Expr::multi_app(
            Expr::var(self.subst_idx),
            smallvec![domain_arg, prop1_arg, rel2_arg],
        ))
    }

    fn get_indep_eq_type(
        &self,
        domain: Expr,
        left: Expr,
        right: Expr,
        _: MinimalContext,
    ) -> Result<Expr> {
        let domain_arg = Arg {
            expr: domain,
            implicit: true,
        };
        let left_arg = Arg {
            expr: left,
            implicit: false,
        };
        let right_arg = Arg {
            expr: right,
            implicit: false,
        };
        Ok(Expr::multi_app(
            Expr::var(self.eq_idx),
            smallvec![domain_arg, left_arg, right_arg],
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
    ) -> Result<Expr> {
        let left_domain_arg = Arg {
            expr: left_domain,
            implicit: true,
        };
        let right_domain_arg = Arg {
            expr: right_domain,
            implicit: true,
        };
        let domain_eq_arg = Arg {
            expr: domain_eq,
            implicit: false,
        };
        let left_arg = Arg {
            expr: left,
            implicit: false,
        };
        let right_arg = Arg {
            expr: right,
            implicit: false,
        };
        Ok(Expr::multi_app(
            Expr::var(self.dep_eq_idx),
            smallvec![
                left_domain_arg,
                right_domain_arg,
                domain_eq_arg,
                left_arg,
                right_arg
            ],
        ))
    }

    fn implicit_arg_max_depth(&self) -> u32 {
        1
    }

    fn placeholder_max_reduction_depth(&self) -> u32 {
        1
    }
}

#[cfg(test)]
mod tests {
    use crate::generic::context_object::*;

    use super::*;

    use anyhow::Result;

    #[test]
    fn test_basics() -> Result<()> {
        let mut mltt = get_mltt();
        mltt.print_all_implicit_args = true;

        let univ = mltt.parse_expr("U")?;

        let pi = mltt.get_constant("Pi").unwrap();
        assert_eq!(mltt.print_expr(&pi.type_expr), "Π {A : U}. (A → U) → U");

        let id_cmb = mltt.get_constant("id").unwrap();
        assert_eq!(mltt.print_expr(&id_cmb.type_expr), "Π A : U. A → A");

        let const_cmb = mltt.get_constant("const").unwrap();
        assert_eq!(
            mltt.print_expr(&const_cmb.type_expr),
            "Π A : U. Π {B : U}. B → A → B"
        );

        let subst_cmb = mltt.get_constant("subst").unwrap();
        assert_eq!(
            mltt.print_expr(&subst_cmb.type_expr),
            "Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. (Π a : A. Pi {P a} (Q a)) → (Π f : Pi {A} P. Π a : A. Q a (f a))"
        );

        let refl = mltt.get_constant("refl").unwrap();
        assert_eq!(
            mltt.print_expr(&refl.type_expr),
            "Π {A : U}. Π a : A. a ={A} a"
        );

        let symm = mltt.get_constant("symm").unwrap();
        assert_eq!(
            mltt.print_expr(&symm.type_expr),
            "Π {A : U}. Π {a : A}. Π {b : A}. a ={A} b → b ={A} a"
        );

        let mut id_ctor = mltt.parse_expr("λ A : U. A")?;
        assert_eq!(mltt.print_expr(&id_ctor), "λ A : U. A");
        let id_ctor_type = mltt.get_expr_type(&id_ctor)?;
        assert_eq!(mltt.print_expr(&id_ctor_type), "U → U");

        let mut const_ctor = mltt.parse_expr("λ A B : U. A")?;
        assert_eq!(mltt.print_expr(&const_ctor), "λ A : U. λ B : U. A");
        let const_ctor_type = mltt.get_expr_type(&const_ctor)?;
        assert_eq!(mltt.print_expr(&const_ctor_type), "U → U → U");

        let const_ctor_occ = mltt.parse_expr("λ A A : U. A⁺")?;
        assert_eq!(mltt.print_expr(&const_ctor_occ), "λ A : U. λ A : U. A⁺");
        assert_eq!(const_ctor_occ, const_ctor);

        let const_id_ctor_occ = mltt.parse_expr("λ A A : U. A")?;
        assert_eq!(mltt.print_expr(&const_id_ctor_occ), "λ A : U. λ A : U. A");
        assert_ne!(const_id_ctor_occ, const_ctor);

        let mut app_u = mltt.parse_expr("λ F : U → U. F U")?;
        let app_u_type = mltt.get_expr_type(&app_u)?;
        assert_eq!(mltt.print_expr(&app_u_type), "(U → U) → U");

        let mut id_fun = mltt.parse_expr("λ A : U. λ a : A. a")?;
        let id_fun_type = mltt.get_expr_type(&id_fun)?;
        assert_eq!(mltt.print_expr(&id_fun_type), "Π A : U. A → A");

        let inner_const_fun = mltt.parse_expr("λ A : U. λ a b : A. a")?;
        assert_eq!(
            mltt.print_expr(&inner_const_fun),
            "λ A : U. λ a : A. λ b : A. a"
        );
        let inner_const_fun_type = mltt.get_expr_type(&inner_const_fun)?;
        assert_eq!(mltt.print_expr(&inner_const_fun_type), "Π A : U. A → A → A");

        let pair_fun = mltt.parse_expr("λ A B : U. λ a : A. λ b : B. Pair_intro A B a b")?;
        let pair_fun_type = mltt.get_expr_type(&pair_fun)?;
        assert_eq!(
            mltt.print_expr(&pair_fun_type),
            "Π A : U. Π B : U. A → B → (A × B)"
        );

        let mut pair_fst_fun =
            mltt.parse_expr("λ A B : U. λ a : A. λ b : B. Pair_fst A B (Pair_intro A B a b)")?;
        let pair_fst_fun_type = mltt.get_expr_type(&pair_fst_fun)?;
        assert_eq!(
            mltt.print_expr(&pair_fst_fun_type),
            "Π A : U. Π B : U. A → B → A"
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
        assert_eq!(mltt.print_expr(&const_ctor), "const U {U}");

        mltt.convert_expr_to_combinators(&mut app_u, -1)?;
        assert_eq!(
            mltt.print_expr(&app_u),
            "subst {Pi {U} (const U {U} U)} {const (Pi {U} (const U {U} U)) {U} U} {const (Pi {U} (const U {U} U)) {Pi {U} (const U {U} U)} (const U {U} U)} (id (Pi {U} (const U {U} U))) (const (Pi {U} (const U {U} U)) {U} U)"
        );
        let app_u_cmb_type = mltt.get_expr_type(&app_u)?;
        assert!(app_u_cmb_type.compare(&app_u_type, &mltt.get_root_context())?);

        mltt.convert_expr_to_combinators(&mut id_fun, -1)?;
        assert_eq!(mltt.print_expr(&id_fun), "id");

        let mut pi_type = pi.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut pi_type, 2)?;
        assert_eq!(
            mltt.print_expr(&pi_type),
            "Pi {U} (subst {U} {λ {A : U}. (A → U) → U} {λ {A : U}. λ _ : (A → U) → U. U} (λ {A : U}. Pi {A → U}) (λ {A : U}. λ _ : A → U. U))"
        );

        let mut id_cmb_type = id_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut id_cmb_type, 2)?;
        assert_eq!(
            mltt.print_expr(&id_cmb_type),
            "Pi {U} (subst {U} {λ A : U. A → U} {λ A : U. λ _ : A → U. U} (λ A : U. Pi {A}) (λ A : U. λ _ : A. A))"
        );
        assert_eq!(mltt.get_expr_type(&id_cmb_type)?, univ);

        let mut const_cmb_type = const_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut const_cmb_type, 2)?;
        assert_eq!(
            mltt.print_expr(&const_cmb_type),
            "Pi {U} (subst {U} {λ A : U. U → U} {λ A : U. λ _ : U → U. U} (λ A : U. Pi {U}) (λ A : U. λ {B : U}. B → A → B))"
        );
        assert_eq!(mltt.get_expr_type(&const_cmb_type)?, univ);

        let mut subst_cmb_type = subst_cmb.type_expr.clone();
        mltt.convert_expr_to_combinators(&mut subst_cmb_type, 2)?;
        assert_eq!(
            mltt.print_expr(&subst_cmb_type),
            "Pi {U} (subst {U} {λ {A : U}. (A → U) → U} {λ {A : U}. λ _ : (A → U) → U. U} (λ {A : U}. Pi {A → U}) (λ {A : U}. λ {P : A → U}. Π {Q : (Π a : A. P a → U)}. (Π a : A. Pi {P a} (Q a)) → (Π f : Pi {A} P. Π a : A. Q a (f a))))"
        );
        assert_eq!(mltt.get_expr_type(&subst_cmb_type)?, univ);

        Ok(())
    }

    #[test]
    fn test_type_errors() -> Result<()> {
        let mltt = get_mltt();

        let non_fun_app = mltt.parse_expr("λ A : U. A A")?;
        assert!(mltt.get_expr_type(&non_fun_app).is_err());

        let app_mismatch = mltt.parse_expr("λ F : U → U. F F")?;
        assert!(mltt.get_expr_type(&app_mismatch).is_err());

        Ok(())
    }

    #[test]
    fn test_type_of_types() -> Result<()> {
        let mltt = get_mltt();
        mltt.check_type_of_types()
    }

    #[test]
    fn test_reduction_rule_types() -> Result<()> {
        let mltt = get_mltt();
        mltt.check_reduction_rule_types()
    }

    // TODO: test that all declared types reduce uniquely (are confluent)
    // TODO: test that specific known terms with multiple reductions are confluent
}
