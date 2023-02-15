use std::collections::HashMap;

use anyhow::Result;
use mimalloc::MiMalloc;
use smallvec::smallvec;

use slate_kernel_generic::context::*;
use slate_kernel_metalogic::{expr::*, helpers::*, metalogic::*};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

pub fn get_mltt() -> MetaLogic {
    MetaLogic::construct_semantically(
        &[
            ModuleInit::Type {
                // For simplicity, we only declare a single universe type `U` with type-in-type.
                // While this would be inconsistent as a foundation, the goal of this theory is not
                // to build a specific foundation but to flesh out and verify the required reduction
                // rules, and to reduce specific terms, i.e. to construct proofs that may be used in
                // theorem provers. So inconsistency is not an issue at this point.
                //
                // (We do have to worry about confluence, as non-confluent reduction rules break
                // subject reduction if they are used in types, which is basically always the case
                // here.)
                ctor: DefInit {
                    sym: "U : U",
                    red: &[]
                },
                defs: &[],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Empty : U",
                    red: &[]
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "Empty_elim : Π A : U. Empty → A",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Empty_isProp : IsProp Empty",
                        red: &["Empty_isProp :≡ λ a. Empty_elim (Π b : Empty. a = b) a"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Unit : U",
                    red: &[]
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "unit : Unit",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Unit_isProp : IsProp Unit",
                        red: &["Unit_isProp :≡ λ _ _. unit"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Unit_isContr : IsContr Unit",
                        red: &["Unit_isContr :≡ Sigma_intro (λ a : Unit. Π b : Unit. a = b) \
                                                            unit \
                                                            (λ _ : Unit. unit)"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Pi : Π {A : U}. (A → U) → U",
                    red: &[],
                },
                defs: &[
                    // Combinators. These should only reduce when all arguments are provided, as
                    // they play a special role when applying reduction rules.
                    ModuleInit::Def(DefInit {
                        sym: "id : Π A : U. A → A",
                        red: &["∀ A : U. ∀ a : A. (id A) a :≡ a"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "const : Π A : U. Π {B : U}. B → (A → B)",
                        red: &["∀ A : U. ∀ {B : U}. ∀ b : B. ∀ a : A. (const A b) a :≡ b"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "substd : Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. \
                                       Pi2d Q → Π f : Pi P. Π a : A. Q a (f a)",
                        red: &["∀ {A : U}. ∀ {P : A → U}. ∀ {Q : (Π a : A. P a → U)}. \
                                ∀ g : Pi2d Q. ∀ f : Pi P. ∀ a : A. \
                                (substd g f) a :≡ g a (f a)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "subst : Π {A B C : U}. (A → B → C) → (A → B) → (A → C)",
                        red: &["subst :≡ λ {A B C}. substd {A} {const A B} {const A (const B C)}"],
                    }),
                    // In contrast, these are just definitions. We could define them in terms of the
                    // above, but that leads to problems because we currently don't reduce
                    // combinators to other combinators.
                    ModuleInit::Def(DefInit {
                        sym: "compd : Π {A B : U}. Π {Q : B → U}. Pi Q → Π f : A → B. Π a : A. Q (f a)",
                        red: &["compd :≡ λ {A B Q}. λ g f a. g (f a)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "comp : Π {A B C : U}. (B → C) → (A → B) → (A → C)",
                        red: &["comp :≡ λ {A B C}. λ g f a. g (f a)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "swapd : Π {A B : U}. Π {Q : A → B → U}. Pi2 Q → Pi2 (Rel_swap Q)",
                        red: &["swapd :≡ λ {A B Q}. λ g. λ b : B. λ a : A. g a b"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "swap : Π {A B C : U}. (A → B → C) → (B → A → C)",
                        red: &["swap :≡ λ {A B C}. λ g b a. g a b"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "swapd_rel : Π {A B : U}. Π Q : A → B → U. Pi2 Q → Pi2 (Rel_swap Q) → U",
                        red: &["swapd_rel :≡ λ {A B}. λ Q f f'. Π a : A. Π b : B. f a b ={Q a b} f' b a"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Pi2d : Π {A : U}. Π {P : A → U}. (Π a : A. P a → U) → U",
                    red: &["Pi2d :≡ λ {A P}. λ Q. Π a : A. Pi (Q a)"],
                },
                defs: &[],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Pi2 : Π {A B : U}. (A → B → U) → U",
                    red: &["Pi2 :≡ λ {A P}. Pi2d {A} {const A P}"],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "Rel_swap : Π {A B : U}. (A → B → U) → (B → A → U)",
                        red: &["Rel_swap :≡ λ {A B}. swap {A} {B} {U}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Rel_comp_1 : Π {A B C : U}. (B → C → U) → (A → B) → (A → C → U)",
                        red: &["Rel_comp_1 :≡ λ {A B C}. λ R f. λ a : A. λ c : C. R (f a) c"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Rel_comp_2 : Π {A B C : U}. (C → B → U) → (A → B) → (C → A → U)",
                        red: &["Rel_comp_2 :≡ λ {A B C}. λ R f. λ c : C. λ a : A. R c (f a)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Fun_to_Rel : Π {A B : U}. (A → B) → (A → B → U)",
                        red: &["Fun_to_Rel :≡ λ {A B}. λ f. λ a : A. λ b : B. f a = b"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Sigma : Π {A : U}. (A → U) → U",
                    red: &[],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "Sigma_intro : Π {A : U}. Π P : A → U. Π a : A. P a → Sigma P",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Sigma_fst : Π {A : U}. Π {P : A → U}. Sigma P → A",
                        red: &["∀ {A : U}. ∀ {P : A → U}. ∀ a : A. ∀ b : P a. \
                                Sigma_fst (Sigma_intro P a b) :≡ a"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Sigma_snd : Π {A : U}. Π {P : A → U}. Π p : Sigma P. P (Sigma_fst p)",
                        red: &["∀ {A : U}. ∀ {P : A → U}. ∀ a : A. ∀ b : P a. \
                                Sigma_snd (Sigma_intro P a b) :≡ b"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Pair_intro : Π A B : U. A → B → (A × B)",
                        red: &["Pair_intro :≡ λ A B. Sigma_intro {A} (λ _. B)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Pair_fst : Π {A B : U}. (A × B) → A",
                        red: &["Pair_fst :≡ λ {A B}. Sigma_fst {A} {λ _. B}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Pair_snd : Π {A B : U}. (A × B) → B",
                        red: &["Pair_snd :≡ λ {A B}. Sigma_snd {A} {λ _. B}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Pair_swap : Π {A B : U}. (A × B) → (B × A)",
                        red: &["Pair_swap :≡ λ {A B}. λ p. Pair_intro B A (Pair_snd p) (Pair_fst p)"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Eq : Π {A : U}. A → A → U",
                    red: &[
                        "Eq {U} :≡ Equiv",
                        "Eq {Unit} :≡ λ _ _. Unit",
                        "∀ {A : U}. ∀ P : A → U. Eq {Pi P} :≡ λ f g. Π a : A. f a = g a",
                        "∀ {A : U}. ∀ P : A → U. \
                         Eq {Sigma P} :≡ λ p q. Σ e_fst : Sigma_fst p = Sigma_fst q. \
                                                Sigma_snd p =[ap P e_fst] Sigma_snd q",
                        "∀ A B : U. Eq {FunRel A B} :≡ λ f g. FunRel_MapsTo f = FunRel_MapsTo g",
                        "∀ A B : U. Eq {Equiv A B} :≡ λ e f. DepEq e = DepEq f",
                    ],
                },
                defs: &[
                    // We treat `refl`, `symm`, and `trans` as (additional) constructors, which we
                    // only reduce in cases where that is compatible with all other operations.
                    ModuleInit::Def(DefInit {
                        sym: "refl : Π {A : U}. Π a : A. a = a",
                        red: &[
                            "refl {U} :≡ Equiv_refl",
                            "refl {Unit} :≡ λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. refl {Pi P} :≡ λ f. λ a : A. refl (f a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             refl {Sigma P} :≡ λ p. Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst p. \
                                                                 Sigma_snd p =[ap P e_fst] Sigma_snd p) \
                                                                (refl (Sigma_fst p)) \
                                                                (DepEq_refl (Sigma_snd p))",
                            "∀ A B : U. refl {FunRel A B} :≡ λ f. refl (FunRel_MapsTo f)",
                            "∀ A B : U. refl {Equiv A B} :≡ λ e. refl (DepEq e)",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        // We define two variants of `trans` that are equal but reduce differently,
                        // for fundamental reasons that have to do with the definition of type
                        // equivalence.
                        // This variant should be used if the second argument is considered the
                        // "primary" one. In particular, `trans` reduces if the first argument is
                        // `refl` but not if the second argument is.
                        sym: "trans : Π {A : U}. Π {a b c : A}. a = b → b = c → a = c",
                        red: &[
                            // Generic reduction.
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. trans (refl a) e :≡ e",
                            // Definitions for each type.
                            "trans {U} :≡ Equiv_trans",
                            "trans {Unit} :≡ λ {_ _ _}. λ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. trans {Pi P} :≡ λ {f g h}. λ efg egh. \
                                                                     λ a : A. trans (efg a) (egh a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             trans {Sigma P} :≡ λ {p q r}. λ epq eqr. \
                                                Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst r. \
                                                             Sigma_snd p =[ap P e_fst] Sigma_snd r) \
                                                            (trans (Sigma_fst epq) (Sigma_fst eqr)) \
                                                            (to (ap_DepEq (symm (ap_f_trans P (Sigma_fst epq) (Sigma_fst eqr))) (Sigma_snd p) (Sigma_snd r)) \
                                                                (DepEq_trans {P (Sigma_fst p)} {P (Sigma_fst q)} {P (Sigma_fst r)} {ap P (Sigma_fst epq)} {ap P (Sigma_fst eqr)} {Sigma_snd p} {Sigma_snd q} {Sigma_snd r} (Sigma_snd epq) (Sigma_snd eqr)))",
                            "∀ A B : U. trans {FunRel A B} :≡ λ {f g h}. trans {A → B → U} {FunRel_MapsTo f} {FunRel_MapsTo g} {FunRel_MapsTo h}",
                            "∀ A B : U. trans {Equiv A B} :≡ λ {e f g}. trans {A → B → U} {DepEq e} {DepEq f} {DepEq g}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        // See above.
                        // This variant should be used if the first argument is considered the
                        // "primary" one. In particular, `trans'` reduces if the second argument is
                        // `refl` but not if the first argument is.
                        sym: "trans' : Π {A : U}. Π {a b c : A}. a = b → b = c → a = c",
                        red: &[
                            // Generic reductions.
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. trans' e (refl b) :≡ e",
                            "∀ {A : U}. ∀ {a b c d : A}. ∀ e : a = b. ∀ f : b = c. ∀ g : c = d. \
                             trans' (trans e f) g :≡ trans e (trans' f g)",
                            // Definitions for each type.
                            "trans' {U} :≡ Equiv_trans'",
                            "trans' {Unit} :≡ λ {_ _ _}. λ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. trans' {Pi P} :≡ λ {f g h}. λ efg egh. \
                                                                      λ a : A. trans' (efg a) (egh a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             trans' {Sigma P} :≡ λ {p q r}. λ epq eqr. \
                                                 Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst r. \
                                                              Sigma_snd p =[ap P e_fst] Sigma_snd r) \
                                                             (trans' (Sigma_fst epq) (Sigma_fst eqr)) \
                                                             (to (ap_DepEq (symm (ap_f_trans' P (Sigma_fst epq) (Sigma_fst eqr))) (Sigma_snd p) (Sigma_snd r)) \
                                                                 (DepEq_trans' {P (Sigma_fst p)} {P (Sigma_fst q)} {P (Sigma_fst r)} {ap P (Sigma_fst epq)} {ap P (Sigma_fst eqr)} {Sigma_snd p} {Sigma_snd q} {Sigma_snd r} (Sigma_snd epq) (Sigma_snd eqr)))",
                            "∀ A B : U. trans' {FunRel A B} :≡ λ {f g h}. trans' {A → B → U} {FunRel_MapsTo f} {FunRel_MapsTo g} {FunRel_MapsTo h}",
                            "∀ A B : U. trans' {Equiv A B} :≡ λ {e f g}. trans' {A → B → U} {DepEq e} {DepEq f} {DepEq g}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "symm : Π {A : U}. Π {a b : A}. a = b → b = a",
                        red: &[
                            // Generic reductions.
                            "∀ {A : U}. ∀ a : A. symm (refl a) :≡ refl a",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. symm (symm e) :≡ e",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. \
                             symm (trans e f) :≡ trans' (symm f) (symm e)",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. \
                             symm (trans' e f) :≡ trans (symm f) (symm e)",
                            // Definitions for each type.
                            "symm {U} :≡ Equiv_symm",
                            "symm {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. symm {Pi P} :≡ λ {f g}. λ e. λ a : A. symm (e a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             symm {Sigma P} :≡ λ {p q}. λ e. \
                                               Sigma_intro (λ e_fst : Sigma_fst q = Sigma_fst p. \
                                                            Sigma_snd q =[ap P e_fst] Sigma_snd p) \
                                                           (symm (Sigma_fst e)) \
                                                           (to (ap_DepEq (symm (ap_f_symm P (Sigma_fst e))) (Sigma_snd q) (Sigma_snd p)) \
                                                               (DepEq_symm {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} {Sigma_snd p} {Sigma_snd q} (Sigma_snd e)))",
                            "∀ A B : U. symm {FunRel A B} :≡ λ {f g}. symm {A → B → U} {FunRel_MapsTo f} {FunRel_MapsTo g}",
                            "∀ A B : U. symm {Equiv A B} :≡ λ {e f}. symm {A → B → U} {DepEq e} {DepEq f}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_eq : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. trans e f = trans' e f",
                        red: &[
                            "trans_eq {U} :≡ λ {A B C}. λ e f. \
                                             Equiv_eq_by_to (trans e f) (trans' e f) (refl (comp (to f) (to e)))",
                            "trans_eq {Unit} :≡ λ {_ _ _}. λ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. trans_eq {Pi P} :≡ λ {f g h}. λ efg egh. \
                                                                        λ a : A. trans_eq (efg a) (egh a)",
                            "∀ {A : U}. ∀ P : A → U. trans_eq {Sigma P} :≡ sorry _",
                            "∀ A B : U. trans_eq {FunRel A B} :≡ \
                                        λ {e f g}. trans_eq {A → B → U} {FunRel_MapsTo e} {FunRel_MapsTo f} {FunRel_MapsTo g}",
                            "∀ A B : U. trans_eq {Equiv A B} :≡ \
                                        λ {e f g}. trans_eq {A → B → U} {DepEq e} {DepEq f} {DepEq g}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_refl : Π {A : U}. Π {a b : A}. Π e : a = b. trans e (refl b) = e",
                        red: &["trans_refl :≡ λ {A a b}. λ e. trans_eq e (refl b)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans'_refl : Π {A : U}. Π {a b : A}. Π e : a = b. trans' (refl a) e = e",
                        red: &["trans'_refl :≡ λ {A a b}. λ e. symm (trans_eq (refl a) e)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_1_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans (symm e) e = refl b",
                        red: &["trans_1_symm :≡ λ {A a b}. λ e. trans_2_symm (symm e)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans'_1_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans' (symm e) e = refl b",
                        red: &["trans'_1_symm :≡ λ {A a b}. λ e. trans'_2_symm (symm e)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_2_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans e (symm e) = refl a",
                        red: &[
                            "trans_2_symm {U} :≡ λ {A B}. λ e. \
                                                 Equiv_eq_by_to (trans e (symm e)) (refl A) (inv_to e)",
                            "trans_2_symm {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. trans_2_symm {Pi P} :≡ λ {f g}. λ e. \
                                                                            λ a : A. trans_2_symm (e a)",
                            "∀ {A : U}. ∀ P : A → U. trans_2_symm {Sigma P} :≡ λ {p q}. λ e. sorry _",
                            "∀ A B : U. trans_2_symm {FunRel A B} :≡ \
                                        λ {e f}. trans_2_symm {A → B → U} {FunRel_MapsTo e} {FunRel_MapsTo f}",
                            "∀ A B : U. trans_2_symm {Equiv A B} :≡ \
                                        λ {e f}. trans_2_symm {A → B → U} {DepEq e} {DepEq f}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans'_2_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans' e (symm e) = refl a",
                        red: &["trans'_2_symm :≡ λ {A a b}. λ e. ap_symm (trans_2_symm e)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3 : Π {A : U}. Π {a b c d : A}. a = b → b = c → c = d → a = d",
                        red: &["trans3 :≡ λ {A a b c d}. λ e f g. trans e (trans' f g)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_1_symm : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. \
                                              trans3 (symm e) e f = f",
                        red: &["trans3_1_symm :≡ λ {A a b c}. λ e f. \
                                                 trans' (ap_trans'_1 (trans_1_symm e) f) (trans'_refl f)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_2_symm : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : a = c. \
                                              trans3 e (symm e) f = f",
                        red: &["trans3_2_symm :≡ λ {A a b c}. λ e f. trans3_1_symm (symm e) f"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans'_1_cancel : Π {A : U}. Π {a b c : A}. Π {e : a = b}. Π {f f' : b = c}. \
                                                trans' e f = trans' e f' → f = f'",
                        red: &["trans'_1_cancel :≡ λ {A a b c e f f'}. λ h. \
                                                   trans3 (symm (trans3_1_symm e f)) \
                                                          (ap_trans_2 (symm e) h) \
                                                          (trans3_1_symm e f')"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_2_symm' : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : c = b. \
                                               trans3 e (symm f) f = e",
                        red: &["trans3_2_symm' :≡ λ {A a b c}. λ e f. trans3_3_symm e (symm f)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_3_symm : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. \
                                              trans3 e f (symm f) = e",
                        red: &["trans3_3_symm :≡ λ {A a b c}. λ e f. \
                                                 trans' (ap_trans_2 e (trans'_2_symm f)) (trans_refl e)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_2_cancel : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. Π {f : b = c}. \
                                               trans e f = trans e' f → e = e'",
                        red: &["trans_2_cancel :≡ λ {A a b c e e' f}. λ h. \
                                                  trans3 (symm (trans3_3_symm e f)) \
                                                         (ap_trans'_1 h (symm f)) \
                                                         (trans3_3_symm e' f)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "symm_rel : Π {A : U}. Π a b : A. (a = b) → (b = a) → U",
                        red: &["symm_rel :≡ λ {A}. λ a b. λ e : a = b. λ f : b = a. e = symm f"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eq_Fun_nat : Π {A B : U}. Π {f g : A → B}. Π efg : f = g. \
                                           Π {a a' : A}. Π ea : a = a'. \
                                           trans (efg a) (ap g ea) = trans' (ap f ea) (efg a')",
                        red: &["Eq_Fun_nat :≡ λ {A B f g}. apd {A} {λ a. f a = g a}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eq_id_nat : Π {A : U}. Π {f : A → A}. Π ef : (Π a : A. f a = a). \
                                          Π {a a' : A}. Π ea : a = a'. \
                                          trans (ef a) ea = trans' (ap f ea) (ef a')",
                        red: &["Eq_id_nat :≡ λ {A f}. Eq_Fun_nat {A} {A} {f} {id A}"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "IsUnique : Π {A : U}. A → U",
                    red: &["IsUnique :≡ λ {A}. λ a. Π b : A. a = b"],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "IsUnique_isProp : Π {A : U}. IsProp A → Π a : A. IsProp (IsUnique a)",
                        red: &["IsUnique_isProp :≡ λ {A}. λ h a. sorry _"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "IsProp : U → U",
                    red: &["IsProp :≡ λ A. Pi (IsUnique {A})"],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "IsProp_to_IsSet : Π A : U. IsProp A → IsSet A",
                        red: &["IsProp_to_IsSet :≡ λ A h. sorry _"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "IsProp_isProp : Π A : U. IsProp (IsProp A)",
                        red: &["IsProp_isProp :≡ λ A. sorry _"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "IsSet : U → U",
                    red: &["IsSet :≡ λ A. Π a b : A. IsProp (a = b)"],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "IsSet_isProp : Π A : U. IsProp (IsSet A)",
                        red: &["IsSet_isProp :≡ λ A. sorry _"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "IsContr : U → U",
                    red: &["IsContr :≡ λ A. Sigma (IsUnique {A})"],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "IsContr_center : Π {A : U}. IsContr A → A",
                        red: &["IsContr_center :≡ λ {A}. Sigma_fst {A} {IsUnique {A}}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "IsContr_unique : Π {A : U}. Π h : IsContr A. IsUnique (IsContr_center h)",
                        red: &["IsContr_unique :≡ λ {A}. Sigma_snd {A} {IsUnique {A}}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "IsContr_to_IsProp : Π A : U. IsContr A → IsProp A",
                        red: &["IsContr_to_IsProp :≡ λ A h. \
                                                     λ a b : A. trans (symm (IsContr_unique h a)) \
                                                                      (IsContr_unique h b)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "IsContr_isProp : Π A : U. IsProp (IsContr A)",
                        red: &["IsContr_isProp :≡ λ A. sorry _"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "IsContr_eq_Eq_Unit : Π A : U. IsContr A = (A = Unit)",
                        red: &["IsContr_eq_Eq_Unit :≡ λ A. sorry _"],
                    }),
                ],
            },
            /*ModuleInit::Type {
                ctor: DefInit {
                    sym: "ContrSigma : Π {A : U}. (A → U) → U",
                    red: &["ContrSigma :≡ λ {A}. λ P. IsContr (Sigma P)"],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "ContrSigma_intro : Π {A : U}. Π P : A → U. Π a : A. Π b : P a. \
                                                 Π ha : (Π a' : A. P a' → a = a'). \
                                                 (Π a' : A. Π b' : P a'. b =[ap P (ha a' b')] b') → \
                                                 ContrSigma P",
                        red: &["ContrSigma_intro :≡ λ {A}. λ P a b ha hb. \
                                                    Sigma_intro (IsUnique {Sigma P}) \
                                                                (Sigma_intro P a b) \
                                                                (λ p' : Sigma P. \
                                                                 Sigma_intro (λ e : a = Sigma_fst p'. b =[ap P e] Sigma_snd p') \
                                                                             (ha (Sigma_fst p') (Sigma_snd p')) \
                                                                             (hb (Sigma_fst p') (Sigma_snd p')))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "ContrSigma_fst : Π {A : U}. Π {P : A → U}. ContrSigma P → A",
                        red: &["ContrSigma_fst :≡ λ {A P}. λ h. Sigma_fst {A} {P} (IsContr_center h)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "ContrSigma_snd : Π {A : U}. Π {P : A → U}. Π h : ContrSigma P. P (ContrSigma_fst h)",
                        red: &["ContrSigma_snd :≡ λ {A P}. λ h. Sigma_snd {A} {P} (IsContr_center h)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "ContrSigma_unique_fst : Π {A : U}. Π {P : A → U}. Π h : ContrSigma P. Π a : A. P a → \
                                                      ContrSigma_fst h = a",
                        red: &["ContrSigma_unique_fst :≡ λ {A P}. λ h a b. \
                                                         Sigma_fst {ContrSigma_fst h = a} \
                                                                   {λ e : ContrSigma_fst h = a. ContrSigma_snd h =[ap P e] b} \
                                                                   (IsContr_unique h (Sigma_intro P a b))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "ContrSigma_unique_snd : Π {A : U}. Π {P : A → U}. Π h : ContrSigma P. Π a : A. Π b : P a. \
                                                      ContrSigma_snd h =[ap P (ContrSigma_unique_fst h a b)] b",
                        red: &["ContrSigma_unique_snd :≡ λ {A P}. λ h a b. \
                                                         Sigma_snd {ContrSigma_fst h = a} \
                                                                   {λ e : ContrSigma_fst h = a. ContrSigma_snd h =[ap P e] b} \
                                                                   (IsContr_unique h (Sigma_intro P a b))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "ContrSigma_isProp : Π {A : U}. Π P : A → U. IsProp (ContrSigma P)",
                        red: &["ContrSigma_isProp :≡ λ {A}. λ P. IsContr_isProp (Sigma P)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "ContrSigma_Eq : Π {A : U}. Π a : A. ContrSigma (Eq a)",
                        red: &["ContrSigma_Eq :≡ λ {A}. λ a. \
                                                 ContrSigma_intro (Eq a) a (refl a) \
                                                                  (λ b : A. λ e : a = b. e) \
                                                                  (λ b : A. λ e : a = b. refl e)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "ContrSigma_swap_Eq : Π {A : U}. Π a : A. ContrSigma ((Rel_swap (Eq {A})) a)",
                        red: &["ContrSigma_swap_Eq :≡ λ {A}. λ a. \
                                                      ContrSigma_intro ((Rel_swap (Eq {A})) a) a (refl a) \
                                                                       (λ b : A. λ e : b = a. symm e) \
                                                                       (λ b : A. λ e : b = a. refl (symm e))"],
                    }),
                ],
            },*/
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "FunRel : U → U → U",
                    red: &[],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_intro : Π {A B : U}. Π R : A → B → U. Π f : A → B. R = Fun_to_Rel f → \
                                             FunRel A B",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_intro_Fun : Π {A B : U}. (A → B) → FunRel A B",
                        red: &["FunRel_intro_Fun :≡ λ {A B}. λ f. \
                                                    FunRel_intro (Fun_to_Rel f) f (refl (Fun_to_Rel f))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_Eq : Π A : U. FunRel A A",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_swap_Eq : Π A : U. FunRel A A",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_comp_1 : Π {A B C : U}. FunRel B C → (A → B) → FunRel A C",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_comp_2 : Π {A B C : U}. Equiv B C → FunRel A B → FunRel A C",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_swapd_rel : Π {A B : U}. Π Q : A → B → U. \
                                                 FunRel (Pi2 Q) (Pi2 (Rel_swap Q))",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_swap_swapd_rel : Π {A B : U}. Π Q : A → B → U. \
                                                      FunRel (Pi2 (Rel_swap Q)) (Pi2 Q)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_symm_rel : Π {A : U}. Π a b : A. FunRel (a = b) (b = a)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_swap_symm_rel : Π {A : U}. Π a b : A. FunRel (b = a) (a = b)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_MapsTo : Π {A B : U}. FunRel A B → A → B → U",
                        red: &[
                            "∀ {A B : U}. ∀ R : A → B → U. ∀ f : A → B. ∀ hf : R = Fun_to_Rel f. \
                             FunRel_MapsTo (FunRel_intro R f hf) :≡ R",
                            "∀ A : U. FunRel_MapsTo (FunRel_Eq A) :≡ Eq {A}",
                            "∀ A : U. FunRel_MapsTo (FunRel_swap_Eq A) :≡ Rel_swap (Eq {A})",
                            "∀ {A B C : U}. ∀ g : FunRel B C. ∀ f : A → B. \
                             FunRel_MapsTo (FunRel_comp_1 g f) :≡ Rel_comp_1 (FunRel_MapsTo g) f",
                            "∀ {A B C : U}. ∀ e : Equiv B C. ∀ f : FunRel A B. \
                             FunRel_MapsTo (FunRel_comp_2 e f) :≡ Rel_comp_2 (FunRel_MapsTo f) (inv e)",
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             FunRel_MapsTo (FunRel_swapd_rel Q) :≡ swapd_rel Q",
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             FunRel_MapsTo (FunRel_swap_swapd_rel Q) :≡ Rel_swap (swapd_rel Q)",
                            "∀ {A : U}. ∀ a b : A. \
                             FunRel_MapsTo (FunRel_symm_rel a b) :≡ symm_rel a b",
                            "∀ {A : U}. ∀ a b : A. \
                             FunRel_MapsTo (FunRel_swap_symm_rel a b) :≡ Rel_swap (symm_rel a b)",
                            "∀ {A B : U}. ∀ e : Equiv A B. FunRel_MapsTo (Equiv_to e) :≡ DepEq e",
                            "∀ {A B : U}. ∀ e : Equiv A B. FunRel_MapsTo (Equiv_inv e) :≡ Rel_swap (DepEq e)",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_fun : Π {A B : U}. FunRel A B → A → B",
                        red: &[
                            "∀ {A B : U}. ∀ R : A → B → U. ∀ f : A → B. ∀ hf : R = Fun_to_Rel f. \
                             FunRel_fun (FunRel_intro R f hf) :≡ f",
                            "∀ A : U. FunRel_fun (FunRel_Eq A) :≡ id A",
                            "∀ A : U. FunRel_fun (FunRel_swap_Eq A) :≡ id A",
                            "∀ {A B C : U}. ∀ g : FunRel B C. ∀ f : A → B. \
                             FunRel_fun (FunRel_comp_1 g f) :≡ comp (FunRel_fun g) f",
                            "∀ {A B C : U}. ∀ e : Equiv B C. ∀ f : FunRel A B. \
                             FunRel_fun (FunRel_comp_2 e f) :≡ comp (to e) (FunRel_fun f)",
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             FunRel_fun (FunRel_swapd_rel Q) :≡ swapd {A} {B} {Q}",
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             FunRel_fun (FunRel_swap_swapd_rel Q) :≡ swapd {B} {A} {Rel_swap Q}",
                            "∀ {A : U}. ∀ a b : A. \
                             FunRel_fun (FunRel_symm_rel a b) :≡ symm {A} {a} {b}",
                            "∀ {A : U}. ∀ a b : A. \
                             FunRel_fun (FunRel_swap_symm_rel a b) :≡ symm {A} {b} {a}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_eq : Π {A B : U}. Π f : FunRel A B. \
                                          FunRel_MapsTo f = Fun_to_Rel (FunRel_fun f)",
                        red: &[
                            "∀ {A B : U}. ∀ R : A → B → U. ∀ f : A → B. ∀ hf : R = Fun_to_Rel f. \
                             FunRel_eq (FunRel_intro R f hf) :≡ hf",
                            "∀ A : U. FunRel_eq (FunRel_Eq A) :≡ λ a b : A. refl (a = b)",
                            "∀ A : U. FunRel_eq (FunRel_swap_Eq A) :≡ λ a b : A. Equiv_symm_rel b a",
                            "∀ {A B C : U}. ∀ g : FunRel B C. ∀ f : A → B. \
                             FunRel_eq (FunRel_comp_1 g f) :≡ λ a : A. λ c : C. (FunRel_eq g) (f a) c",
                            "∀ {A B C : U}. ∀ e : Equiv B C. ∀ f : FunRel A B. \
                             FunRel_eq (FunRel_comp_2 e f) :≡ λ a : A. λ c : C. \
                                                              trans {U} {FunRel_MapsTo f a (inv e c)} {FunRel_fun f a = inv e c} {to e (FunRel_fun f a) = c} \
                                                                    ((FunRel_eq f) a (inv e c)) (symm (to_inv_eq e (FunRel_fun f a) c))",
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             FunRel_eq (FunRel_swapd_rel Q) :≡ λ f : Pi2 Q. λ f' : Pi2 (Rel_swap Q). \
                                                               Equiv_swapd_rel (λ a : A. λ b : B. f a b ={Q a b} f' b a)",
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             FunRel_eq (FunRel_swap_swapd_rel Q) :≡ λ f' : Pi2 (Rel_swap Q). λ f : Pi2 Q. \
                                                                    apd (Pi2 {A} {B}) \
                                                                        {λ a : A. λ b : B. f a b ={Q a b} f' b a} \
                                                                        {λ a : A. λ b : B. f' b a ={Q a b} f a b} \
                                                                        (λ a : A. λ b : B. Equiv_symm_rel {Q a b} (f a b) (f' b a))",
                            "∀ {A : U}. ∀ a b : A. \
                             FunRel_eq (FunRel_symm_rel a b) :≡ λ e : a = b. λ f : b = a. \
                                                                ape {a = b} {b = a} (Equiv_symm_rel a b) e (symm f)",
                            "∀ {A : U}. ∀ a b : A. \
                             FunRel_eq (FunRel_swap_symm_rel a b) :≡ λ f : b = a. λ e : a = b. \
                                                                     Equiv_symm_rel e (symm f)",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_inst : Π {A B : U}. Π f : FunRel A B. Π a : A. \
                                            FunRel_MapsTo f a (FunRel_fun f a)",
                        red: &["FunRel_inst :≡ λ {A B}. λ f a. \
                                               inv ((FunRel_eq f) a (FunRel_fun f a)) \
                                                   (refl (FunRel_fun f a))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "FunRel_unique : Π {A B : U}. Π f : FunRel A B. \
                                              Π a : A. Π b : B. FunRel_MapsTo f a b → \
                                              FunRel_fun f a = b",
                        red: &["FunRel_unique :≡ λ {A B}. λ f a b. to ((FunRel_eq f) a b)"],
                    }),
                    ModuleInit::Def(DefInit {
                        // This shows that our version of equivalence is equivalent to the
                        // "bijective relation" variant in the HoTT book.
                        // TODO: The proof currently uses a strange reverse path induction. We
                        // should reduce it to the underlying application of `apd` once it is done,
                        // to see if it can be simplified that way.
                        sym: "FunRel_inst_unique : Π {A B : U}. Π f : FunRel A B. \
                                                   Π a : A. Π b : B. Π hRab : FunRel_MapsTo f a b. \
                                                   FunRel_inst f a =[ap (FunRel_MapsTo f a) (FunRel_unique f a b hRab)] hRab",
                        red: &["FunRel_inst_unique :≡ λ {A B}. λ f a b hRab. \
                                                        [h1 : inv ((FunRel_eq f) a b) (FunRel_unique f a b hRab) = hRab \
                                                            ⫽ inv_to {FunRel_MapsTo f a b} {FunRel_fun f a = b} ((FunRel_eq f) a b) hRab] \
                                                        [h2 : ap (FunRel_MapsTo f a) (trans (symm (FunRel_unique f a b hRab)) \
                                                                                    (FunRel_unique f a b hRab)) = \
                                                              refl (FunRel_MapsTo f a b) \
                                                            ⫽ ap_ap (FunRel_MapsTo f a) (trans_1_symm (FunRel_unique f a b hRab))] \
                                                        [h3 : inv ((FunRel_eq f) a b) (FunRel_unique f a b hRab) \
                                                              =[ap (FunRel_MapsTo f a) (trans (symm (FunRel_unique f a b hRab)) \
                                                                                      (FunRel_unique f a b hRab))] \
                                                              hRab \
                                                            ⫽ inv (ap_DepEq h2 (inv ((FunRel_eq f) a b) (FunRel_unique f a b hRab)) hRab) h1] \
                                                        trd_rl (λ b' : B. λ e : FunRel_fun f a = b'. \
                                                                inv ((FunRel_eq f) a b') e \
                                                                =[ap (FunRel_MapsTo f a) (trans (symm e) (FunRel_unique f a b hRab))] \
                                                                hRab) \
                                                               (FunRel_unique f a b hRab) \
                                                               h3"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Equiv : U → U → U",
                    red: &[],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_intro : Π {A B : U}. Π R : A → B → U. \
                                            Π f : A → B. R = Fun_to_Rel f → \
                                            Π g : B → A. Rel_swap R = Fun_to_Rel g → \
                                            Equiv A B",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_intro_Fun' : Π {A B : U}. Π f : A → B. Π g : B → A. \
                                                 Rel_swap (Fun_to_Rel f) = Fun_to_Rel g → \
                                                 Equiv A B",
                        red: &["Equiv_intro_Fun' :≡ λ {A B}. λ f. \
                                                    Equiv_intro (Fun_to_Rel f) f (refl (Fun_to_Rel f))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_intro_Fun : Π {A B : U}. Π f : A → B. Π g : B → A. \
                                                Fun_to_Rel f = Rel_swap (Fun_to_Rel g) → \
                                                Equiv A B",
                        red: &["Equiv_intro_Fun :≡ λ {A B}. λ f g hfg. \
                                                   Equiv_intro_Fun' f g (swapd {A} {B} \
                                                                               {λ a b. (f a = b) = (g b = a)} \
                                                                               hfg)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_refl : Π A : U. Equiv A A",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_trans : Π {A B C : U}. Equiv A B → Equiv B C → Equiv A C",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_trans' : Π {A B C : U}. Equiv A B → Equiv B C → Equiv A C",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_symm : Π {A B : U}. Equiv A B → Equiv B A",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_swapd_rel : Π {A B : U}. Π Q : A → B → U. \
                                                Equiv (Pi2 Q) (Pi2 (Rel_swap Q))",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_swap_rel : Π A B C : U. Equiv (A → B → C) (B → A → C)",
                        red: &["Equiv_swap_rel :≡ λ A B C. Equiv_swapd_rel (const A (const B C))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_symm_rel : Π {A : U}. Π a b : A. Equiv (a = b) (b = a)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_trans_1_rel : Π {A : U}. Π {a a' : A}. a = a' → Π b : A. Equiv (a = b) (a' = b)",
                        red: &["Equiv_trans_1_rel :≡ λ {A}. λ {a a'}. λ e. λ b. \
                                                  Equiv_intro (λ f : a = b. λ f' : a' = b. f = trans e f') \
                                                              (λ f : a = b. trans' (symm e) f) \
                                                              (sorry _) \
                                                              (λ f : a' = b. trans' e f) \
                                                              (sorry _)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_trans_2_rel : Π {A : U}. Π a : A. Π {b b' : A}. b = b' → Equiv (a = b) (a = b')",
                        red: &["Equiv_trans_2_rel :≡ λ {A}. λ a. λ {b b'}. λ e. \
                                                  Equiv_intro (λ f : a = b. λ f' : a = b'. trans f e = f') \
                                                              (λ f : a = b. trans f e) \
                                                              (sorry _) \
                                                              (λ f : a = b'. trans f (symm e)) \
                                                              (sorry _)"],
                    }),
                    ModuleInit::Type {
                        ctor: DefInit {
                            sym: "DepEq : Π {A B : U}. Equiv A B → A → B → U",
                            red: &[
                                // We could delegate everything to `Equiv_to` here, but we want `DepEq` to
                                // reduce late so that its notation is preserved where applicable.
                                "∀ {A B : U}. ∀ R : A → B → U. \
                                 ∀ f : A → B. ∀ hf : R = Fun_to_Rel f. \
                                 ∀ g : B → A. ∀ hg : Rel_swap R = Fun_to_Rel g. \
                                 DepEq (Equiv_intro R f hf g hg) :≡ R",
                                "∀ A : U. DepEq (Equiv_refl A) :≡ Eq {A}",
                                "∀ {A B C : U}. ∀ e : Equiv A B. ∀ f : Equiv B C. \
                                 DepEq (Equiv_trans e f) :≡ Rel_comp_1 (DepEq f) (to e)",
                                "∀ {A B C : U}. ∀ e : Equiv A B. ∀ f : Equiv B C. \
                                 DepEq (Equiv_trans' e f) :≡ Rel_comp_2 (DepEq e) (inv f)",
                                "∀ {A B : U}. ∀ e : Equiv A B. DepEq (Equiv_symm e) :≡ Rel_swap (DepEq e)",
                                "∀ {A B : U}. ∀ Q : A → B → U. DepEq (Equiv_swapd_rel Q) :≡ swapd_rel Q",
                                "∀ {A : U}. ∀ a b : A. DepEq (Equiv_symm_rel a b) :≡ symm_rel a b",
                            ],
                        },
                        defs: &[
                            ModuleInit::Def(DefInit {
                                sym: "DepEq_to : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. \
                                                 (a =[eAB] b) = (to eAB a = b)",
                                red: &["DepEq_to :≡ λ {A B}. λ eAB. FunRel_eq (Equiv_to eAB)"],
                            }),
                            ModuleInit::Def(DefInit {
                                sym: "DepEq_inv' : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. \
                                                   (a =[eAB] b) = (inv eAB b = a)",
                                red: &["DepEq_inv' :≡ λ {A B}. λ eAB a b. (FunRel_eq (Equiv_inv eAB)) b a"],
                            }),
                            ModuleInit::Def(DefInit {
                                sym: "DepEq_inv : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. \
                                                  (a =[eAB] b) = (a = inv eAB b)",
                                red: &["DepEq_inv :≡ λ {A B}. λ eAB a b. \
                                                     trans' (DepEq_inv' eAB a b) (Equiv_symm_rel (inv eAB b) a)"],
                            }),
                            ModuleInit::Def(DefInit {
                                sym: "DepEq_refl : Π {A : U}. Π a : A. a =[refl A] a",
                                red: &["DepEq_refl :≡ refl"],
                            }),
                            ModuleInit::Def(DefInit {
                                sym: "DepEq_symm : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. \
                                                   a =[eAB] b → b =[symm eAB] a",
                                red: &["DepEq_symm :≡ λ {A B eAB a b}. id (a =[eAB] b)"],
                            }),
                            ModuleInit::Def(DefInit {
                                sym: "DepEq_trans_Eq : Π {A B : U}. Π {eAB : A = B}. Π {a a' : A}. Π {b : B}. \
                                                       a = a' → a' =[eAB] b → a =[eAB] b",
                                red: &["DepEq_trans_Eq :≡ λ {A B eAB a a' b}. λ e f. \
                                                          inv (DepEq_inv eAB a b) \
                                                              (trans e (to (DepEq_inv eAB a' b) f))"],
                            }),
                            ModuleInit::Def(DefInit {
                                sym: "DepEq_trans'_Eq : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b b' : B}. \
                                                        a =[eAB] b → b = b' → a =[eAB] b'",
                                red: &["DepEq_trans'_Eq :≡ λ {A B eAB a b b'}. λ e f. \
                                                           inv (DepEq_to eAB a b') \
                                                               (trans' (to (DepEq_to eAB a b) e) f)"],
                            }),
                            ModuleInit::Def(DefInit {
                                sym: "DepEq_trans : Π {A B C : U}. Π {eAB : A = B}. Π {eBC : B = C}. \
                                                    Π {a : A}. Π {b : B}. Π {c : C}. \
                                                    a =[eAB] b → b =[eBC] c → a =[trans eAB eBC] c",
                                red: &["DepEq_trans :≡ λ {A B C eAB eBC a b c}. λ e f. \
                                                       DepEq_trans_Eq {B} {C} {eBC} {to eAB a} {b} {c} \
                                                                      (to (DepEq_to eAB a b) e) f"],
                            }),
                            ModuleInit::Def(DefInit {
                                sym: "DepEq_trans' : Π {A B C : U}. Π {eAB : A = B}. Π {eBC : B = C}. \
                                                     Π {a : A}. Π {b : B}. Π {c : C}. \
                                                     a =[eAB] b → b =[eBC] c → a =[trans' eAB eBC] c",
                                red: &["DepEq_trans' :≡ λ {A B C eAB eBC a b c}. λ e f. \
                                                        DepEq_trans'_Eq {A} {B} {eAB} {a} {b} {inv eBC c} \
                                                                        e (to (DepEq_inv eBC b c) f)"],
                            }),
                        ],
                    },
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_to : Π {A B : U}. Equiv A B → FunRel A B",
                        red: &[
                            "∀ {A B : U}. ∀ R : A → B → U. \
                             ∀ f : A → B. ∀ hf : R = Fun_to_Rel f. \
                             ∀ g : B → A. ∀ hg : Rel_swap R = Fun_to_Rel g. \
                             Equiv_to (Equiv_intro R f hf g hg) :≡ FunRel_intro R f hf",
                            "∀ A : U. Equiv_to (Equiv_refl A) :≡ FunRel_Eq A",
                            "∀ {A B C : U}. ∀ e : Equiv A B. ∀ f : Equiv B C. \
                             Equiv_to (Equiv_trans e f) :≡ FunRel_comp_1 (Equiv_to f) (to e)",
                            "∀ {A B C : U}. ∀ e : Equiv A B. ∀ f : Equiv B C. \
                             Equiv_to (Equiv_trans' e f) :≡ FunRel_comp_2 f (Equiv_to e)",
                            "∀ {A B : U}. ∀ e : Equiv A B. \
                             Equiv_to (Equiv_symm e) :≡ Equiv_inv e",
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             Equiv_to (Equiv_swapd_rel Q) :≡ FunRel_swapd_rel Q",
                            "∀ {A : U}. ∀ a b : A. \
                             Equiv_to (Equiv_symm_rel a b) :≡ FunRel_symm_rel a b",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_inv : Π {A B : U}. Equiv A B → FunRel B A",
                        red: &[
                            "∀ {A B : U}. ∀ R : A → B → U. \
                             ∀ f : A → B. ∀ hf : R = Fun_to_Rel f. \
                             ∀ g : B → A. ∀ hg : Rel_swap R = Fun_to_Rel g. \
                             Equiv_inv (Equiv_intro R f hf g hg) :≡ FunRel_intro (Rel_swap R) g hg",
                            "∀ A : U. Equiv_inv (Equiv_refl A) :≡ FunRel_swap_Eq A",
                            "∀ {A B C : U}. ∀ e : Equiv A B. ∀ f : Equiv B C. \
                             Equiv_inv (Equiv_trans e f) :≡ FunRel_comp_2 (Equiv_symm e) (Equiv_inv f)",
                            "∀ {A B C : U}. ∀ e : Equiv A B. ∀ f : Equiv B C. \
                             Equiv_inv (Equiv_trans' e f) :≡ FunRel_comp_1 (Equiv_inv e) (inv f)",
                            "∀ {A B : U}. ∀ e : Equiv A B. \
                             Equiv_inv (Equiv_symm e) :≡ Equiv_to e",
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             Equiv_inv (Equiv_swapd_rel Q) :≡ FunRel_swap_swapd_rel Q",
                            "∀ {A : U}. ∀ a b : A. \
                             Equiv_inv (Equiv_symm_rel a b) :≡ FunRel_swap_symm_rel a b",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "to : Π {A B : U}. Equiv A B → A → B",
                        red: &["to :≡ λ {A B}. λ e. FunRel_fun (Equiv_to e)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "inv : Π {A B : U}. Equiv A B → B → A",
                        red: &["inv :≡ λ {A B}. λ e. FunRel_fun (Equiv_inv e)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "to_inv_eq : Π {A B : U}. Π e : Equiv A B. Π a : A. Π b : B. (to e a = b) = (a = inv e b)",
                        red: &["to_inv_eq :≡ λ {A B}. λ e a b. trans' (symm (DepEq_to e a b)) (DepEq_inv e a b)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "inv_to : Π {A B : U}. Π e : Equiv A B. Π a : A. inv e (to e a) = a",
                        red: &["inv_to :≡ λ {A B}. λ e a. \
                                          FunRel_unique (Equiv_inv e) (to e a) a (FunRel_inst (Equiv_to e) a)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "to_inv : Π {A B : U}. Π e : Equiv A B. Π b : B. to e (inv e b) = b",
                        red: &["to_inv :≡ λ {A B}. λ e b. \
                                          FunRel_unique (Equiv_to e) (inv e b) b (FunRel_inst (Equiv_inv e) b)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Equiv_eq_by_to : Π {A B : U}. Π e e' : Equiv A B. to e = to e' → e = e'",
                        red: &["Equiv_eq_by_to :≡ λ {A B}. λ e e' h. \
                                                  λ a : A. λ b : B. trans3 (DepEq_to e a b) \
                                                                           (ap (λ f : A → B. f a = b) h) \
                                                                           (symm (DepEq_to e' a b))"],
                    }),
                ],
            },
            ModuleInit::Def(DefInit {
                sym: "ap : Π {A B : U}. Π f : A → B. Π {a a' : A}. a = a' → f a = f a'",
                red: &[
                    // We could simply define `ap` as a special case of `apd`. However,
                    // non-dependent application generally yields much simpler terms, and it often
                    // appears in types, so we explicitly specify non-dependent variants of all
                    // cases here.
                    "∀ {A B : U}. ∀ f : A → B. ∀ a : A. ap f (refl a) :≡ refl (f a)",
                    // -- Type constructors --
                    "∀ A : U. ap (Pi {A}) :≡ ap_Pi {A}",
                    "∀ B : U. ap (λ A : U. A → B) :≡ λ {A A'}. λ eA. ap_Fun_1 eA B",
                    // TODO: This specialization should not be necessary.
                    // Apparently, conversion of the lambda term to combinators fails in some way.
                    "∀ B C : U. ap (λ A : U. (A → B) → C) :≡ λ {A A'}. λ eA. ap_Fun_1 (ap_Fun_1 eA B) C",
                    "∀ {A : U}. ∀ a : A. ap (Eq a) :≡ Equiv_trans_2_rel a",
                    "∀ A : U. ap (Eq {A}) :≡ Equiv_trans_1_rel {A}",
                    "∀ {A B : U}. ∀ eAB : A = B. ∀ a : A. ap (DepEq eAB a) :≡ ap_DepEq_3 eAB a",
                    "∀ {A B : U}. ∀ eAB : A = B. ap (DepEq eAB) :≡ ap_DepEq_2 eAB",
                    "∀ {A B : U}. ap (DepEq {A} {B}) :≡ ap_DepEq {A} {B}",
                    // TODO
                    // -- Combinators --
                    "∀ A : U. ap (id A) :≡ λ {a a'}. λ e. e",
                    "∀ A : U. ∀ {B : U}. ∀ b : B. ap (const A b) :≡ λ {a a'}. λ e. refl b",
                    "∀ A B : U. ap (const A {B}) :≡ λ {b b'}. λ e. λ a : A. e",
                    "∀ {A B C : U}. ∀ g : A → B → C. ∀ f : A → B. ap (subst g f) :≡ ap_subst' g f",
                    "∀ {A B C : U}. ∀ g : A → B → C. ap (subst g) :≡ λ {f f'}. λ e. λ a : A. ap (g a) (e a)",
                    "∀ A B C : U. ap (subst {A} {B} {C}) :≡ λ {g g'}. λ e. λ f : A → B. λ a : A. e a (f a)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ {C : U}. ∀ g : (Π a : A. P a → C). ∀ f : Pi P. \
                     ap {A} {C} (substd {A} {P} {λ a. const (P a) C} g f) :≡ ap_substd' g f",
                    "∀ {A B : U}. ∀ {Q : A → U}. ∀ g : (Π a : A. B → Q a). \
                     ap {A → B} {Pi Q} (substd {A} {const A B} {λ a. const B (Q a)} g) :≡ \
                     λ {f f'}. λ e. λ a : A. ap (g a) (e a)",
                    // -- Other functions --
                    "∀ {A B : U}. ∀ f : A → B. ∀ a a' : A. ap (ap f {a} {a'}) :≡ ap_ap f {a} {a'}",
                    "∀ {A : U}. ∀ a b : A. ap (symm {A} {a} {b}) :≡ ap_symm {A} {a} {b}",
                    "∀ {A : U}. ∀ a b c : A. ∀ e : a = b. ap (trans {A} {a} {b} {c} e) :≡ ap_trans_2 {A} {a} {b} {c} e",
                    "∀ {A : U}. ∀ a b c : A. ∀ e : a = b. ap (trans' {A} {a} {b} {c} e) :≡ ap_trans'_2 {A} {a} {b} {c} e",
                    "∀ {A : U}. ∀ a b c : A. ap (trans {A} {a} {b} {c}) :≡ ap_trans_1 {A} {a} {b} {c}",
                    "∀ {A : U}. ∀ a b c : A. ap (trans' {A} {a} {b} {c}) :≡ ap_trans'_1 {A} {a} {b} {c}",
                    // TODO lots more
                ],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_Pi : Π {A : U}. Π {P P' : A → U}. Π eP : P = P'. Pi P = Pi P'",
                red: &["ap_Pi :≡ λ {A P P'}. λ eP. \
                                 Equiv_intro (λ f : Pi P. λ f' : Pi P'. Π a : A. f a =[eP a] f' a) \
                                             (λ f : Pi P. λ a : A. to (eP a) (f a)) \
                                             (sorry _) \
                                             (λ f' : Pi P'. λ a : A. inv (eP a) (f' a)) \
                                             (sorry _)"], // λ f : Pi P. λ f' : Pi P'. ap_Pi (λ a : A. DepEq_to (eP a) (f a) (f' a))
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_Fun_1 : Π {A A' : U}. Π eA : A = A'. Π B : U. (A → B) = (A' → B)",
                red: &["ap_Fun_1 :≡ λ {A A'}. λ eA B. \
                                    Equiv_intro (λ f : A → B. λ f' : A' → B. \
                                                 Π a : A. Π a' : A'. a =[eA] a' → f a = f' a') \
                                                (λ f : A → B. λ a' : A'. f (inv eA a')) \
                                                (sorry _) \
                                                (λ f' : A' → B. λ a : A. f' (to eA a)) \
                                                (sorry _)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_DepEq : Π {A B : U}. Π {eAB eAB' : A = B}. Π heAB : eAB = eAB'. Π a : A. Π b : B. \
                                 (a =[eAB] b) = (a =[eAB'] b)",
                red: &["ap_DepEq :≡ λ {A B eAB eAB'}. λ heAB a b. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_DepEq_2 : Π {A B : U}. Π eAB : A = B. Π {a a' : A}. Π ea : a = a'. Π b : B. \
                                   (a =[eAB] b) = (a' =[eAB] b)",
                red: &["ap_DepEq_2 :≡ λ {A B}. λ eAB. λ {a a'}. λ ea b. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_DepEq_3 : Π {A B : U}. Π eAB : A = B. Π a : A. Π {b b' : B}. Π eb : b = b'. \
                                   (a =[eAB] b) = (a =[eAB] b')",
                red: &["ap_DepEq_3 :≡ λ {A B}. λ eAB a. λ {b b'}. λ eb. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_subst : Π {A B C : U}. Π g : A → B → C. Π f : A → B. Π {a a' : A}. Π e : a = a'. \
                                 subst g f a = subst g f a'",
                red: &["ap_subst :≡ λ {A B C}. λ g f. λ {a a'}. λ e. \
                                    trans {C} {g a (f a)} {g a' (f a)} {g a' (f a')} \
                                          ((ap g e) (f a)) (ap (g a') (ap f e))"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_subst' : Π {A B C : U}. Π g : A → B → C. Π f : A → B. Π {a a' : A}. Π e : a = a'. \
                                  subst g f a = subst g f a'",
                // Note: It is important that we use `trans'` here, not `trans`, so that `ap` on
                // function composition reduces nicely due to the second argument of `trans'`
                // becoming `refl` when `g` is constant on `A`.
                red: &["ap_subst' :≡ λ {A B C}. λ g f. λ {a a'}. λ e. \
                                     trans' {C} {g a (f a)} {g a (f a')} {g a' (f a')} \
                                            (ap (g a) (ap f e)) ((ap g e) (f a'))"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_subst_nat : Π {A B C : U}. Π g : A → B → C. Π f : A → B. Π {a a' : A}. Π e : a = a'. \
                                     ap_subst g f e = ap_subst' g f e",
                red: &["ap_subst_nat :≡ λ {A B C}. λ g f. λ {a a'}. λ e. \
                                        Eq_Fun_nat {B} {C} {g a} {g a'} (ap g e) (ap f e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_substd : Π {A : U}. Π {P : A → U}. Π {C : U}. \
                                  Π g : (Π a : A. P a → C). Π f : Pi P. Π {a a' : A}. Π e : a = a'. \
                                  substd {A} {P} {λ a. const (P a) C} g f a = \
                                  substd {A} {P} {λ a. const (P a) C} g f a'",
                red: &["ap_substd :≡ λ {A P C}. λ g f. λ {a a'}. λ e. \
                                     sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_substd' : Π {A : U}. Π {P : A → U}. Π {C : U}. \
                                   Π g : (Π a : A. P a → C). Π f : Pi P. Π {a a' : A}. Π e : a = a'. \
                                   substd {A} {P} {λ a. const (P a) C} g f a = \
                                   substd {A} {P} {λ a. const (P a) C} g f a'",
                red: &["ap_substd' :≡ λ {A P C}. λ g f. λ {a a'}. λ e. \
                                      sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_substd_nat : Π {A : U}. Π {P : A → U}. Π {C : U}. \
                                      Π g : (Π a : A. P a → C). Π f : Pi P. Π {a a' : A}. Π e : a = a'. \
                                      ap_substd g f e = ap_substd' g f e",
                red: &["ap_substd_nat :≡ λ {A P C}. λ g f. λ {a a'}. λ e. \
                                         sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_ap : Π {A B : U}. Π f : A → B. Π {a a' : A}. Π {e e' : a = a'}. \
                              e = e' → ap f e = ap f e'",
                red: &["ap_ap :≡ λ {A B}. λ f. λ {a a'}. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_symm : Π {A : U}. Π {a b : A}. Π {e e' : a = b}. e = e' → symm e = symm e'",
                red: &["ap_symm :≡ λ {A a b e e'}. λ he. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_trans_1 : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π f : b = c. \
                                   trans e f = trans e' f",
                red: &["ap_trans_1 :≡ λ {A a b c e e'}. λ he f. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_trans'_1 : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π f : b = c. \
                                    trans' e f = trans' e' f",
                red: &["ap_trans'_1 :≡ λ {A a b c e e'}. λ he f. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_trans_2 : Π {A : U}. Π {a b c : A}. Π e : a = b. Π {f f' : b = c}. f = f' → \
                                   trans e f = trans e f'",
                red: &["ap_trans_2 :≡ λ {A a b c}. λ e. λ {f f'}. λ hf. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_trans'_2 : Π {A : U}. Π {a b c : A}. Π e : a = b. Π {f f' : b = c}. f = f' → \
                                    trans' e f = trans' e f'",
                red: &["ap_trans'_2 :≡ λ {A a b c}. λ e. λ {f f'}. λ hf. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_trans : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π {f f' : b = c}. f = f' → \
                                 trans e f = trans e' f'",
                red: &["ap_trans :≡ λ {A a b c e e'}. λ he. λ {f f'}. λ hf. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_trans' : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π {f f' : b = c}. f = f' → \
                                  trans' e f = trans' e' f'",
                red: &["ap_trans' :≡ λ {A a b c e e'}. λ he. λ {f f'}. λ hf. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_f_symm : Π {A B : U}. Π f : A → B. Π {a b : A}. Π e : a = b. \
                                  ap f (symm e) = symm (ap f e)",
                red: &["ap_f_symm :≡ sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_f_trans : Π {A B : U}. Π f : A → B. Π {a b c : A}. Π eab : a = b. Π ebc : b = c. \
                                   ap f (trans eab ebc) = trans (ap f eab) (ap f ebc)",
                red: &["ap_f_trans :≡ sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_f_trans' : Π {A B : U}. Π f : A → B. Π {a b c : A}. Π eab : a = b. Π ebc : b = c. \
                                    ap f (trans' eab ebc) = trans' (ap f eab) (ap f ebc)",
                red: &["ap_f_trans' :≡ sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apd : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a a' : A}. Π e : a = a'. f a =[ap P e] f a'",
                red: &[
                    "∀ A B : U. apd {A} {const A B} :≡ ap {A} {B}", // See comment at `ap`.
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ a : A. apd f (refl a) :≡ DepEq_refl (f a)",
                    // -- Type constructors --
                    "apd Pi :≡ λ {A A'}. λ eA. \
                               λ P : A → U. λ P' : A' → U. \
                               λ hP : (Π {a : A}. Π {a' : A'}. a =[eA] a' → P a = P' a'). \
                               Equiv_intro (λ f : Pi P. λ f' : Pi P'. \
                                            Π {a : A}. Π {a' : A'}. Π ea : a =[eA] a'. \
                                            f a =[hP ea] f' a') \
                                           (sorry _) (sorry _) (sorry _) (sorry _)",
                    // TODO
                    // -- Combinators --
                    "∀ {A : U}. ∀ {P : A → U}. ∀ {Q : (Π a : A. P a → U)}. ∀ g : Pi2d Q. ∀ f : Pi P. \
                     apd (substd g f) :≡ sorry _",
                    // TODO
                    // -- Other functions --
                    // TODO
                ],
            }),
            /*DefInit {
                sym: "apd_substd : Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. \
                                   Π g : Pi2d Q. Π f : Pi P. Π {a a' : A}. Π e : a = a'. \
                                   substd g f a =[] substd g f a'",
                red: &["apd_substd :≡ λ {A P Q}. λ g f. λ {a a'}. λ e. \
                                      trans {} {g a (f a)} {g a' (f a)} {g a' (f a')} \
                                            ((apd g e) (f a)) (apd (g a') (apd f e))"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apd_substd' : Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. \
                                    Π g : Pi2d Q. Π f : Pi P. Π {a a' : A}. Π e : a = a'. \
                                    substd g f a =[] substd g f a'",
                red: &["apd_substd' :≡ λ {A P Q}. λ g f. λ {a a'}. λ e. \
                                       trans' {} {g a (f a)} {g a (f a')} {g a' (f a')} \
                                              (apd (g a) (apd f e)) ((apd g e) (f a'))"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apd_substd_nat : Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. \
                                       Π g : Pi2d Q. Π f : Pi P. Π {a a' : A}. Π e : a = a'. \
                                       apd_substd g f e = apd_substd' g f e",
                red: &["apd_substd_nat :≡ λ {A P Q}. λ g f. λ {a a'}. λ e. \
                                          sorry _"],
            }),*/
            ModuleInit::Def(DefInit {
                sym: "apd_f_symm : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a b : A}. Π e : a = b. \
                                   apd f (symm e) =[ap_DepEq (ap_f_symm P e) (f b) (f a)] DepEq_symm (apd f e)",
                red: &["apd_f_symm :≡ sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apd_f_trans : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a b c : A}. Π eab : a = b. Π ebc : b = c. \
                                    apd f (trans eab ebc) =[ap_DepEq (ap_f_trans P eab ebc) (f a) (f c)] DepEq_trans (apd f eab) (apd f ebc)",
                red: &["apd_f_trans :≡ sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apd_f_trans' : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a b c : A}. Π eab : a = b. Π ebc : b = c. \
                                     apd f (trans' eab ebc) =[ap_DepEq (ap_f_trans' P eab ebc) (f a) (f c)] DepEq_trans' (apd f eab) (apd f ebc)",
                red: &["apd_f_trans' :≡ sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "tr_lr : Π {A : U}. Π P : A → U. Π {a a' : A}. a = a' → P a → P a'",
                red: &["tr_lr :≡ λ {A}. λ P. λ {a a'}. λ e. to (ap P e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "tr_rl : Π {A : U}. Π P : A → U. Π {a a' : A}. a = a' → P a' → P a",
                red: &["tr_rl :≡ λ {A}. λ P. λ {a a'}. λ e. inv (ap P e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ape : Π {A B : U}. Π e : A = B. Π a a' : A. (a = a') = (to e a = to e a')",
                red: &["ape :≡ λ {A B}. λ e a a'. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apj : Π {A : U}. Π {a a' : A}. Π P : (Π b : A. a = b → U). Π e : a = a'. P a (refl a) = P a' e",
                red: &["apj :≡ λ {A a a'}. λ P e. sorry _"], // trans3 _ ((apd P e) e) _)
            }),
            ModuleInit::Def(DefInit {
                sym: "trd_lr : Π {A : U}. Π {a a' : A}. Π P : (Π b : A. a = b → U). Π e : a = a'. P a (refl a) → P a' e",
                red: &["trd_lr :≡ λ {A a a'}. λ P e. to (apj P e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "trd_rl : Π {A : U}. Π {a a' : A}. Π P : (Π b : A. a = b → U). Π e : a = a'. P a' e → P a (refl a)",
                red: &["trd_rl :≡ λ {A a a'}. λ P e. inv (apj P e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry : Π A : U. A", // TODO: remove once everything is filled
                red: &["∀ {A : U}. ∀ a : A. sorry (a = a) :≡ refl a"], // to reduce temporary failures
            }),
        ],
        |constants| Box::new(MLTTLambdaHandler::new(constants)),
    )
    .unwrap()
}

struct MLTTLambdaHandler {
    u_idx: VarIndex,
    pi_idx: VarIndex,
    sigma_idx: VarIndex,
    id_idx: VarIndex,
    const_idx: VarIndex,
    substd_idx: VarIndex,
    eq_idx: VarIndex,
    dep_eq_idx: VarIndex,
}

impl MLTTLambdaHandler {
    fn new(constants: &HashMap<&str, VarIndex>) -> Self {
        MLTTLambdaHandler {
            u_idx: *constants.get("U").unwrap(),
            pi_idx: *constants.get("Pi").unwrap(),
            sigma_idx: *constants.get("Sigma").unwrap(),
            id_idx: *constants.get("id").unwrap(),
            const_idx: *constants.get("const").unwrap(),
            substd_idx: *constants.get("substd").unwrap(),
            eq_idx: *constants.get("Eq").unwrap(),
            dep_eq_idx: *constants.get("DepEq").unwrap(),
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
            Expr::var(self.substd_idx),
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
    use anyhow::Result;

    use slate_kernel_generic::context_object::*;
    use slate_kernel_metalogic::metalogic_context::*;

    use super::*;

    #[test]
    fn test_mltt() -> Result<()> {
        env_logger::init();

        // Test everything in sequence so that errors during construction only appear once.
        // (And because construction takes a while.)
        let mltt = get_mltt();

        test_basics(&mltt)?;
        test_type_errors(&mltt)?;
        test_type_of_types(&mltt)?;
        test_reduction_rule_types(&mltt)?;

        Ok(())
    }

    fn test_basics(mltt: &MetaLogic) -> Result<()> {
        let root_ctx = mltt.get_root_context_with_options(MetaLogicContextOptions {
            print_all_implicit_args: true,
            ..mltt.root_ctx_options
        });

        let univ = Expr::parse("U", &root_ctx)?;

        let pi = mltt.get_constant("Pi").unwrap();
        assert_eq!(pi.type_expr.print(&root_ctx), "Π {A : U}. (A → U) → U");

        let id_cmb = mltt.get_constant("id").unwrap();
        assert_eq!(id_cmb.type_expr.print(&root_ctx), "Π A : U. A → A");

        let const_cmb = mltt.get_constant("const").unwrap();
        assert_eq!(
            const_cmb.type_expr.print(&root_ctx),
            "Π A : U. Π {B : U}. B → A → B"
        );

        let subst_cmb = mltt.get_constant("substd").unwrap();
        assert_eq!(
            subst_cmb.type_expr.print(&root_ctx),
            "Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. Pi2d {A} {P} Q → (Π f : Pi {A} P. Π a : A. Q a (f a))"
        );

        let refl = mltt.get_constant("refl").unwrap();
        assert_eq!(
            refl.type_expr.print(&root_ctx),
            "Π {A : U}. Π a : A. a ={A} a"
        );

        let symm = mltt.get_constant("symm").unwrap();
        assert_eq!(
            symm.type_expr.print(&root_ctx),
            "Π {A : U}. Π {a : A}. Π {b : A}. a ={A} b → b ={A} a"
        );

        let mut id_ctor = Expr::parse("λ A : U. A", &root_ctx)?;
        assert_eq!(id_ctor.print(&root_ctx), "λ A : U. A");
        let id_ctor_type = id_ctor.get_type(&root_ctx)?;
        assert_eq!(id_ctor_type.print(&root_ctx), "U → U");

        let mut const_ctor = Expr::parse("λ A B : U. A", &root_ctx)?;
        assert_eq!(const_ctor.print(&root_ctx), "λ A : U. λ B : U. A");
        let const_ctor_type = const_ctor.get_type(&root_ctx)?;
        assert_eq!(const_ctor_type.print(&root_ctx), "U → U → U");

        let const_ctor_occ = Expr::parse("λ A A : U. A⁺", &root_ctx)?;
        assert_eq!(const_ctor_occ.print(&root_ctx), "λ A : U. λ A' : U. A");
        assert_eq!(const_ctor_occ, const_ctor);

        let const_id_ctor_occ = Expr::parse("λ A A : U. A", &root_ctx)?;
        assert_eq!(const_id_ctor_occ.print(&root_ctx), "λ A : U. λ A' : U. A'");
        assert_ne!(const_id_ctor_occ, const_ctor);

        let mut app_u = Expr::parse("λ F : U → U. F U", &root_ctx)?;
        let app_u_type = app_u.get_type(&root_ctx)?;
        assert_eq!(app_u_type.print(&root_ctx), "(U → U) → U");

        let mut id_fun = Expr::parse("λ A : U. λ a : A. a", &root_ctx)?;
        let id_fun_type = id_fun.get_type(&root_ctx)?;
        assert_eq!(id_fun_type.print(&root_ctx), "Π A : U. A → A");

        let inner_const_fun = Expr::parse("λ A : U. λ a b : A. a", &root_ctx)?;
        assert_eq!(
            inner_const_fun.print(&root_ctx),
            "λ A : U. λ a : A. λ b : A. a"
        );
        let inner_const_fun_type = inner_const_fun.get_type(&root_ctx)?;
        assert_eq!(inner_const_fun_type.print(&root_ctx), "Π A : U. A → A → A");

        let pair_fun = Expr::parse("λ A B : U. λ a : A. λ b : B. Pair_intro A B a b", &root_ctx)?;
        let pair_fun_type = pair_fun.get_type(&root_ctx)?;
        assert_eq!(
            pair_fun_type.print(&root_ctx),
            "Π A : U. Π B : U. A → B → (A × B)"
        );

        let mut pair_fst_fun = Expr::parse(
            "λ A B : U. λ a : A. λ b : B. Pair_fst {A} {B} (Pair_intro A B a b)",
            &root_ctx,
        )?;
        let pair_fst_fun_type = pair_fst_fun.get_type(&root_ctx)?;
        assert_eq!(
            pair_fst_fun_type.print(&root_ctx),
            "Π A : U. Π B : U. A → B → A"
        );
        let pair_fst_fun_reduced = pair_fst_fun.reduce(&root_ctx, -1)?;
        assert!(pair_fst_fun_reduced);
        assert_eq!(
            pair_fst_fun.print(&root_ctx),
            "λ A : U. λ B : U. λ a : A. λ b : B. a"
        );

        id_ctor.convert_to_combinators(&root_ctx, -1)?;
        assert_eq!(id_ctor.print(&root_ctx), "id U");

        const_ctor.convert_to_combinators(&root_ctx, -1)?;
        assert_eq!(const_ctor.print(&root_ctx), "const U {U}");

        app_u.convert_to_combinators(&root_ctx, -1)?;
        assert_eq!(
            app_u.print(&root_ctx),
            "substd {Pi {U} (const U {U} U)} {const (Pi {U} (const U {U} U)) {U} U} {const (Pi {U} (const U {U} U)) {Pi {U} (const U {U} U)} (const U {U} U)} (id (Pi {U} (const U {U} U))) (const (Pi {U} (const U {U} U)) {U} U)"
        );
        let app_u_cmb_type = app_u.get_type(&root_ctx)?;
        assert!(app_u_cmb_type.compare(&app_u_type, &mltt.get_root_context())?);

        id_fun.convert_to_combinators(&root_ctx, -1)?;
        assert_eq!(id_fun.print(&root_ctx), "id");

        let mut pi_type = pi.type_expr.clone();
        pi_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            pi_type.print(&root_ctx),
            "Pi {U} (substd {U} {λ {A : U}. (A → U) → U} {λ {A : U}. λ _ : (A → U) → U. U} (λ {A : U}. Pi {A → U}) (λ {A : U}. λ _ : A → U. U))"
        );

        let mut id_cmb_type = id_cmb.type_expr.clone();
        id_cmb_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            id_cmb_type.print(&root_ctx),
            "Pi {U} (substd {U} {λ A : U. A → U} {λ A : U. λ _ : A → U. U} (λ A : U. Pi {A}) (λ A : U. λ _ : A. A))"
        );
        assert_eq!(id_cmb_type.get_type(&root_ctx)?, univ);

        let mut const_cmb_type = const_cmb.type_expr.clone();
        const_cmb_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            const_cmb_type.print(&root_ctx),
            "Pi {U} (substd {U} {λ A : U. U → U} {λ A : U. λ _ : U → U. U} (λ A : U. Pi {U}) (λ A : U. λ {B : U}. B → A → B))"
        );
        assert_eq!(const_cmb_type.get_type(&root_ctx)?, univ);

        let mut subst_cmb_type = subst_cmb.type_expr.clone();
        subst_cmb_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            subst_cmb_type.print(&root_ctx),
            "Pi {U} (substd {U} {λ {A : U}. (A → U) → U} {λ {A : U}. λ _ : (A → U) → U. U} (λ {A : U}. Pi {A → U}) (λ {A : U}. λ {P : A → U}. Π {Q : (Π a : A. P a → U)}. Pi2d {A} {P} Q → (Π f : Pi {A} P. Π a : A. Q a (f a))))"
        );
        assert_eq!(subst_cmb_type.get_type(&root_ctx)?, univ);

        Ok(())
    }

    fn test_type_errors(mltt: &MetaLogic) -> Result<()> {
        let root_ctx = mltt.get_root_context();

        let non_fun_app = Expr::parse("λ A : U. A A", &root_ctx)?;
        assert!(non_fun_app.get_type(&root_ctx).is_err());

        let app_mismatch = Expr::parse("λ F : U → U. F F", &root_ctx)?;
        assert!(app_mismatch.get_type(&root_ctx).is_err());

        Ok(())
    }

    fn test_type_of_types(mltt: &MetaLogic) -> Result<()> {
        mltt.check_type_of_types()
    }

    fn test_reduction_rule_types(mltt: &MetaLogic) -> Result<()> {
        mltt.check_reduction_rule_types()
    }

    // TODO: check equality of variable names in defs
    // TODO: test confluence (in general, or just of all concrete terms)
}
