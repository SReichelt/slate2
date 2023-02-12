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
            TypeInit {
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
                    DefInit {
                        sym: "Empty_isProp : IsProp Empty",
                        red: &["Empty_isProp :≡ λ a. Empty_elim (Π b : Empty. a = b) a"],
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
                    DefInit {
                        sym: "Unit_isProp : IsProp Unit",
                        red: &["Unit_isProp :≡ λ _ _. unit"],
                    },
                    DefInit {
                        sym: "Unit_isContr : IsContr Unit",
                        red: &["Unit_isContr :≡ Sigma_intro (λ a : Unit. Π b : Unit. a = b) \
                                                            unit \
                                                            (λ _ : Unit. unit)"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Pi : Π {A : U}. (A → U) → U",
                    red: &[],
                },
                defs: &[
                    // Combinators. These should only reduce when all arguments are provided, as
                    // they play a special role when applying reduction rules.
                    DefInit {
                        sym: "id : Π A : U. A → A",
                        red: &["∀ A : U. ∀ a : A. (id A) a :≡ a"],
                    },
                    DefInit {
                        sym: "const : Π A : U. Π {B : U}. B → (A → B)",
                        red: &["∀ A : U. ∀ {B : U}. ∀ b : B. ∀ a : A. (const A b) a :≡ b"],
                    },
                    DefInit {
                        sym: "subst : Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. \
                                      Pi2d Q → Π f : Pi P. Π a : A. Q a (f a)",
                        red: &["∀ {A : U}. ∀ {P : A → U}. ∀ {Q : (Π a : A. P a → U)}. ∀ g : Pi2d Q. ∀ f : Pi P. ∀ a : A. \
                                (subst g f) a :≡ g a (f a)"],
                    },
                    // In contrast, these are just definitions. We could define them in terms of the
                    // above, but that leads to problems because we currently don't reduce
                    // combinators to other combinators.
                    DefInit {
                        sym: "compd : Π {A B : U}. Π {Q : B → U}. Pi Q → Π f : A → B. Π a : A. Q (f a)",
                        red: &["compd :≡ λ {A B Q}. λ g f a. g (f a)"],
                    },
                    DefInit {
                        sym: "comp : Π {A B C : U}. (B → C) → (A → B) → (A → C)",
                        red: &["comp :≡ λ {A B C}. λ g f a. g (f a)"],
                    },
                    DefInit {
                        sym: "swapd : Π {A B : U}. Π {Q : A → B → U}. Pi2 Q → Pi2 (Rel_swap Q)",
                        red: &["swapd :≡ λ {A B Q}. λ g. λ b : B. λ a : A. g a b"],
                    },
                    DefInit {
                        sym: "swap : Π {A B C : U}. (A → B → C) → (B → A → C)",
                        red: &["swap :≡ λ {A B C}. λ g b a. g a b"],
                    },
                    DefInit {
                        sym: "swapd_rel : Π A B : U. Π Q : A → B → U. Pi2 Q → Pi2 (Rel_swap Q) → U",
                        red: &["swapd_rel :≡ λ A B Q. λ f f'. Π a : A. Π b : B. f a b ={Q a b} f' b a"],
                    },
                    DefInit {
                        sym: "swapd_is_Eq : Π A B : U. Π Q : A → B → U. Pi2 Q = Pi2 (Rel_swap Q)",
                        red: &["swapd_is_Eq :≡ λ A B Q. Eq_U_intro' (swapd_rel A B Q) \
                                                                    (IsFunRel_swapd_rel A B Q) \
                                                                    (IsFunRel_swap_swapd_rel A B Q)"],
                    },
                    DefInit {
                        sym: "swap_is_Eq : Π A B C : U. (A → B → C) = (B → A → C)",
                        red: &["swap_is_Eq :≡ λ A B C. swapd_is_Eq A B (const A (const B C))"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Pi2d : Π {A : U}. Π {P : A → U}. (Π a : A. P a → U) → U",
                    red: &["Pi2d :≡ λ {A P}. λ Q. Π a : A. Pi (Q a)"],
                },
                defs: &[],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Pi2 : Π {A B : U}. (A → B → U) → U",
                    red: &["Pi2 :≡ λ {A P}. Pi2d {A} {const A P}"],
                },
                defs: &[
                    DefInit {
                        sym: "Rel_swap : Π {A B : U}. (A → B → U) → (B → A → U)",
                        red: &["Rel_swap :≡ λ {A B}. swap {A} {B} {U}"],
                    },
                    DefInit {
                        sym: "Rel_comp_1 : Π {A B C : U}. (B → C → U) → (A → B) → (A → C → U)",
                        red: &["Rel_comp_1 :≡ λ {A B C}. λ R f. λ a : A. λ c : C. R (f a) c"],
                    },
                    DefInit {
                        sym: "Rel_comp_2 : Π {A B C : U}. (C → B → U) → (A → B) → (C → A → U)",
                        red: &["Rel_comp_2 :≡ λ {A B C}. λ R f. λ c : C. λ a : A. R c (f a)"],
                    },
                    DefInit {
                        sym: "Fun_to_Rel : Π {A B : U}. (A → B) → (A → B → U)",
                        red: &["Fun_to_Rel :≡ λ {A B}. λ f. λ a : A. λ b : B. f a = b"],
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
                        red: &["∀ {A : U}. ∀ {P : A → U}. ∀ a : A. ∀ b : P a. \
                                Sigma_fst (Sigma_intro P a b) :≡ a"],
                    },
                    DefInit {
                        sym: "Sigma_snd : Π {A : U}. Π {P : A → U}. Π p : Sigma P. P (Sigma_fst p)",
                        red: &["∀ {A : U}. ∀ {P : A → U}. ∀ a : A. ∀ b : P a. \
                                Sigma_snd (Sigma_intro P a b) :≡ b"],
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
                    DefInit {
                        sym: "Pair_swap : Π {A B : U}. (A × B) → (B × A)",
                        red: &["Pair_swap :≡ λ {A B}. λ p. Pair_intro B A (Pair_snd p) (Pair_fst p)"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Eq : Π {A : U}. A → A → U",
                    red: &[
                        // We give explicit definitions of `Eq` for all type constructors except
                        // `U`. For `U`, we define type equivalence axiomatically, mostly for
                        // performance but also because it allows us to treat equality of type
                        // equivalences specially, which is nice because we can just omit the
                        // contractible `IsBijRel` part.
                        "Eq {Unit} :≡ λ _ _. Unit",
                        "∀ {A : U}. ∀ P : A → U. Eq {Pi P} :≡ λ f g. Π a : A. f a = g a",
                        "∀ {A : U}. ∀ P : A → U. Eq {Sigma P} :≡ λ p q. Σ e_fst : Sigma_fst p = Sigma_fst q. \
                                                                        Sigma_snd p =[ap P e_fst] Sigma_snd q",
                        "∀ A B : U. Eq {A = B} :≡ λ e f. Eq_rel e = Eq_rel f",
                    ],
                },
                defs: &[
                    DefInit {
                        sym: "Eq_U_intro : Π {A B : U}. Π R : A → B → U. IsBijRel R → A = B",
                        red: &[],
                    },
                    DefInit {
                        sym: "Eq_U_intro' : Π {A B : U}. Π R : A → B → U. IsFunRel R → IsFunRel (Rel_swap R) → \
                                            A = B",
                        red: &["Eq_U_intro' :≡ λ {A B}. λ R hTo hInv. \
                                               Eq_U_intro R (IsBijRel_intro hTo hInv)"],
                    },
                    DefInit {
                        sym: "Eq_U_intro'' : Π {A B : U}. Π R : A → B → U. \
                                             Π to : A → B. R = Fun_to_Rel to → \
                                             Π inv : B → A. Rel_swap R = Fun_to_Rel inv → \
                                             A = B",
                        red: &["Eq_U_intro'' :≡ λ {A B}. λ R to hTo inv hInv. \
                                                Eq_U_intro' R (IsFunRel_intro R to hTo) \
                                                              (IsFunRel_intro (Rel_swap R) inv hInv)"],
                    },
                    // We treat `refl`, `symm`, and `trans` as (additional) constructors, which we
                    // only reduce in cases where that is compatible with all other operations.
                    DefInit {
                        sym: "refl : Π {A : U}. Π a : A. a = a",
                        red: &[
                            "refl {Unit} :≡ λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. refl {Pi P} :≡ λ f. λ a : A. refl (f a)",
                            "∀ {A : U}. ∀ P : A → U. refl {Sigma P} :≡ λ p. Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst p. Sigma_snd p =[ap P e_fst] Sigma_snd p) \
                                                                                        (refl (Sigma_fst p)) \
                                                                                        (DepEq_refl (Sigma_snd p))",
                            "∀ A B : U. refl {A = B} :≡ λ e. refl (Eq_rel e)",
                        ],
                    },
                    DefInit {
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
                            "trans {Unit} :≡ λ {_ _ _}. λ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. trans {Pi P} :≡ λ {f g h}. λ efg egh. λ a : A. trans (efg a) (egh a)",
                            "∀ {A : U}. ∀ P : A → U. trans {Sigma P} :≡ λ {p q r}. λ epq eqr. Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst r. Sigma_snd p =[ap P e_fst] Sigma_snd r) \
                                                                                                          (trans {A} {Sigma_fst p} {Sigma_fst q} {Sigma_fst r} (Sigma_fst epq) (Sigma_fst eqr)) \
                                                                                                          (sorry _)", // DepEq_trans {P (Sigma_fst p)} {P (Sigma_fst q)} {P (Sigma_fst r)} {ap P (Sigma_fst epq)} {ap P (Sigma_fst eqr)} {Sigma_snd p} {Sigma_snd q} {Sigma_snd r} (Sigma_snd epq) (Sigma_snd eqr)
                            "∀ A B : U. trans {A = B} :≡ λ {e f g}. trans {A → B → U} {Eq_rel e} {Eq_rel f} {Eq_rel g}",
                        ],
                    },
                    DefInit {
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
                            "trans' {Unit} :≡ λ {_ _ _}. λ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. trans' {Pi P} :≡ λ {f g h}. λ efg egh. λ a : A. trans' (efg a) (egh a)",
                            "∀ {A : U}. ∀ P : A → U. trans' {Sigma P} :≡ λ {p q r}. λ epq eqr. Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst r. Sigma_snd p =[ap P e_fst] Sigma_snd r) \
                                                                                                           (trans' {A} {Sigma_fst p} {Sigma_fst q} {Sigma_fst r} (Sigma_fst epq) (Sigma_fst eqr)) \
                                                                                                           (sorry _)", // DepEq_trans' {P (Sigma_fst p)} {P (Sigma_fst q)} {P (Sigma_fst r)} {ap P (Sigma_fst epq)} {ap P (Sigma_fst eqr)} {Sigma_snd p} {Sigma_snd q} {Sigma_snd r} (Sigma_snd epq) (Sigma_snd eqr)
                            "∀ A B : U. trans' {A = B} :≡ λ {e f g}. trans' {A → B → U} {Eq_rel e} {Eq_rel f} {Eq_rel g}",
                        ],
                    },
                    DefInit {
                        sym: "symm : Π {A : U}. Π {a b : A}. a = b → b = a",
                        red: &[
                            // Generic reductions.
                            "∀ {A : U}. ∀ a : A. symm (refl a) :≡ refl a",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. symm (symm e) :≡ e",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. symm (trans e f) :≡ trans' (symm f) (symm e)",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. symm (trans' e f) :≡ trans (symm f) (symm e)",
                            // Definitions for each type.
                            "symm {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. symm {Pi P} :≡ λ {f g}. λ e. λ a : A. symm (e a)",
                            "∀ {A : U}. ∀ P : A → U. symm {Sigma P} :≡ λ {p q}. λ e. Sigma_intro (λ e_fst : Sigma_fst q = Sigma_fst p. Sigma_snd q =[ap P e_fst] Sigma_snd p) \
                                                                                                 (symm {A} {Sigma_fst p} {Sigma_fst q} (Sigma_fst e)) \
                                                                                                 (sorry _)", // DepEq_symm {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} {Sigma_snd p} {Sigma_snd q} (Sigma_snd e)
                            "∀ A B : U. symm {A = B} :≡ λ {e f}. symm {A → B → U} {Eq_rel e} {Eq_rel f}",
                        ],
                    },
                    DefInit {
                        sym: "Eq_rel : Π {A B : U}. A = B → (A → B → U)",
                        red: &[
                            "∀ {A B : U}. ∀ R : A → B → U. ∀ h : IsBijRel R. Eq_rel (Eq_U_intro R h) :≡ R",
                            "∀ A : U. Eq_rel (refl A) :≡ Eq {A}",
                            "∀ {A B C : U}. ∀ e : A = B. ∀ f : B = C. Eq_rel (trans e f) :≡ Rel_comp_1 (Eq_rel f) (to e)",
                            "∀ {A B C : U}. ∀ e : A = B. ∀ f : B = C. Eq_rel (trans' e f) :≡ Rel_comp_2 (Eq_rel e) (inv f)",
                            "∀ {A B : U}. ∀ e : A = B. Eq_rel (symm e) :≡ Rel_swap (Eq_rel e)",
                        ],
                    },
                    DefInit {
                        sym: "Eq_isBijRel : Π {A B : U}. Π e : A = B. IsBijRel (Eq_rel e)",
                        red: &[
                            "∀ {A B : U}. ∀ R : A → B → U. ∀ h : IsBijRel R. Eq_isBijRel (Eq_U_intro R h) :≡ h",
                            "∀ A : U. Eq_isBijRel (refl A) :≡ IsBijRel_Eq A",
                            "∀ {A B C : U}. ∀ e : A = B. ∀ f : B = C. Eq_isBijRel (trans e f) :≡ IsBijRel_comp_1 (Eq_isBijRel f) e",
                            "∀ {A B C : U}. ∀ e : A = B. ∀ f : B = C. Eq_isBijRel (trans' e f) :≡ IsBijRel_comp_2 f (Eq_isBijRel e)",
                            "∀ {A B : U}. ∀ e : A = B. Eq_isBijRel (symm e) :≡ IsBijRel_swap (Eq_isBijRel e)",
                        ],
                    },
                    DefInit {
                        sym: "to : Π {A B : U}. A = B → A → B",
                        red: &["to :≡ λ {A B}. λ e. IsFunRel_to (IsBijRel_to_isFunRel (Eq_isBijRel e))"],
                    },
                    DefInit {
                        sym: "inv : Π {A B : U}. A = B → B → A",
                        red: &["inv :≡ λ {A B}. λ e. IsFunRel_to (IsBijRel_inv_isFunRel (Eq_isBijRel e))"],
                    },
                    DefInit {
                        sym: "Eq_rel_to : Π {A B : U}. Π e : A = B. Π a : A. Π b : B. ((Eq_rel e) a b) = (to e a = b)",
                        red: &["Eq_rel_to :≡ λ {A B}. λ e. IsFunRel_eq (IsBijRel_to_isFunRel (Eq_isBijRel e))"],
                    },
                    DefInit {
                        sym: "Eq_rel_inv' : Π {A B : U}. Π e : A = B. Π a : A. Π b : B. ((Eq_rel e) a b) = (inv e b = a)",
                        red: &["Eq_rel_inv' :≡ λ {A B}. λ e a b. (IsFunRel_eq (IsBijRel_inv_isFunRel (Eq_isBijRel e))) b a"],
                    },
                    DefInit {
                        sym: "Eq_rel_inv : Π {A B : U}. Π e : A = B. Π a : A. Π b : B. ((Eq_rel e) a b) = (a = inv e b)",
                        red: &["Eq_rel_inv :≡ λ {A B}. λ e a b. trans' (Eq_rel_inv' e a b) (symm_is_Eq (inv e b) a)"],
                    },
                    DefInit {
                        sym: "Eq_to_inv_eq : Π {A B : U}. Π e : A = B. Π a : A. Π b : B. (to e a = b) = (a = inv e b)",
                        red: &["Eq_to_inv_eq :≡ λ {A B}. λ e a b. trans (symm (Eq_rel_to e a b)) (Eq_rel_inv e a b)"],
                    },
                    DefInit {
                        sym: "inv_to : Π {A B : U}. Π e : A = B. Π a : A. inv e (to e a) = a",
                        red: &["inv_to :≡ λ {A B}. λ e a. \
                                          IsFunRel_unique (IsBijRel_inv_isFunRel (Eq_isBijRel e)) \
                                                          (to e a) \
                                                          a \
                                                          (IsFunRel_inst (IsBijRel_to_isFunRel (Eq_isBijRel e)) a)"],
                    },
                    DefInit {
                        sym: "to_inv : Π {A B : U}. Π e : A = B. Π b : B. to e (inv e b) = b",
                        red: &["to_inv :≡ λ {A B}. λ e. inv_to (symm e)"],
                    },
                    DefInit {
                        sym: "Eq_U_eq_by_to : Π {A B : U}. Π e e' : A = B. to e = to e' → e = e'",
                        red: &["Eq_U_eq_by_to :≡ λ {A B}. λ e e' h. λ a : A. λ b : B. \
                                                                    trans3 (Eq_rel_to e a b) \
                                                                           (ap (λ f : A → B. f a = b) h) \
                                                                           (symm (Eq_rel_to e' a b))"],
                    },
                    DefInit {
                        sym: "trans_eq : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. trans e f = trans' e f",
                        red: &[
                            "trans_eq {U} :≡ λ {A B C}. λ e f. Eq_U_eq_by_to (trans e f) \
                                                                             (trans' e f) \
                                                                             (refl (comp (to f) (to e)))",
                            "trans_eq {Unit} :≡ λ {_ _ _}. λ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. trans_eq {Pi P} :≡ λ {f g h}. λ efg egh. λ a : A. trans_eq (efg a) (egh a)",
                            "∀ {A : U}. ∀ P : A → U. trans_eq {Sigma P} :≡ sorry _",
                            "∀ A B : U. trans_eq {A = B} :≡ λ {e f g}. trans_eq {A → B → U} {Eq_rel e} {Eq_rel f} {Eq_rel g}",
                        ],
                    },
                    DefInit {
                        sym: "trans_refl : Π {A : U}. Π {a b : A}. Π e : a = b. trans e (refl b) = e",
                        red: &["trans_refl :≡ λ {A a b}. λ e. trans_eq e (refl b)"],
                    },
                    DefInit {
                        sym: "trans'_refl : Π {A : U}. Π {a b : A}. Π e : a = b. trans' (refl a) e = e",
                        red: &["trans'_refl :≡ λ {A a b}. λ e. symm (trans_eq (refl a) e)"],
                    },
                    DefInit {
                        sym: "trans_1_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans (symm e) e = refl b",
                        red: &["trans_1_symm :≡ λ {A a b}. λ e. trans_2_symm (symm e)"],
                    },
                    DefInit {
                        sym: "trans'_1_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans' (symm e) e = refl b",
                        red: &["trans'_1_symm :≡ λ {A a b}. λ e. trans'_2_symm (symm e)"],
                    },
                    DefInit {
                        sym: "trans_2_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans e (symm e) = refl a",
                        red: &[
                            "trans_2_symm {U} :≡ λ {A B}. λ e. Eq_U_eq_by_to (trans e (symm e)) \
                                                                             (refl A) \
                                                                             (sorry _)", // TODO: matching bug?
                            "trans_2_symm {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. trans_2_symm {Pi P} :≡ λ {f g}. λ e. λ a : A. trans_2_symm (e a)",
                            "∀ {A : U}. ∀ P : A → U. trans_2_symm {Sigma P} :≡ λ {p q}. λ e. sorry _",
                            "∀ A B : U. trans_2_symm {A = B} :≡ λ {e f}. trans_2_symm {A → B → U} {Eq_rel e} {Eq_rel f}",
                        ],
                    },
                    DefInit {
                        sym: "trans'_2_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans' e (symm e) = refl a",
                        red: &["trans'_2_symm :≡ λ {A a b}. λ e. ap_symm (trans_2_symm e)"],
                    },
                    DefInit {
                        sym: "trans3 : Π {A : U}. Π {a b c d : A}. a = b → b = c → c = d → a = d",
                        red: &["trans3 :≡ λ {A a b c d}. λ e f g. trans e (trans' f g)"],
                    },
                    DefInit {
                        sym: "trans3_1_symm : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. trans3 (symm e) e f = f",
                        red: &["trans3_1_symm :≡ λ {A a b c}. λ e f. trans' (ap_trans'_1 (trans_1_symm e) f) (trans'_refl f)"],
                    },
                    DefInit {
                        sym: "trans3_2_symm : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : a = c. trans3 e (symm e) f = f",
                        red: &["trans3_2_symm :≡ λ {A a b c}. λ e f. trans3_1_symm (symm e) f"],
                    },
                    DefInit {
                        sym: "trans'_1_cancel : Π {A : U}. Π {a b c : A}. Π {e : a = b}. Π {f f' : b = c}. trans' e f = trans' e f' → f = f'",
                        red: &["trans'_1_cancel :≡ λ {A a b c e f f'}. λ h. trans3 (symm (trans3_1_symm e f)) (ap_trans_2 (symm e) h) (trans3_1_symm e f')"],
                    },
                    DefInit {
                        sym: "trans3_2_symm' : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : c = b. trans3 e (symm f) f = e",
                        red: &["trans3_2_symm' :≡ λ {A a b c}. λ e f. trans3_3_symm e (symm f)"],
                    },
                    DefInit {
                        sym: "trans3_3_symm : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. trans3 e f (symm f) = e",
                        red: &["trans3_3_symm :≡ λ {A a b c}. λ e f. trans' (ap_trans_2 e (trans'_2_symm f)) (trans_refl e)"],
                    },
                    DefInit {
                        sym: "trans_2_cancel : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. Π {f : b = c}. trans e f = trans e' f → e = e'",
                        red: &["trans_2_cancel :≡ λ {A a b c e e' f}. λ h. trans3 (symm (trans3_3_symm e f)) (ap_trans'_1 h (symm f)) (trans3_3_symm e' f)"],
                    },
                    DefInit {
                        sym: "symm_is_Eq : Π {A : U}. Π a b : A. (a = b) = (b = a)",
                        red: &["symm_is_Eq :≡ λ {A}. λ a b. \
                                              Eq_U_intro'' (λ e : a = b. λ f : b = a. e = symm f) \
                                                           (symm {A} {a} {b}) \
                                                           (sorry _) \
                                                           (symm {A} {b} {a}) \
                                                           (sorry _)"],
                    },
                    DefInit {
                        sym: "trans_1_is_Eq : Π {A : U}. Π {a a' : A}. a = a' → Π b : A. (a = b) = (a' = b)",
                        red: &["trans_1_is_Eq :≡ λ {A}. λ {a a'}. λ e. λ b. \
                                                 Eq_U_intro'' (λ f : a = b. λ f' : a' = b. f = trans e f') \
                                                              (λ f : a = b. trans' (symm e) f) \
                                                              (sorry _) \
                                                              (λ f : a' = b. trans' e f) \
                                                              (sorry _)"],
                    },
                    DefInit {
                        sym: "trans_2_is_Eq : Π {A : U}. Π a : A. Π {b b' : A}. b = b' → (a = b) = (a = b')",
                        red: &["trans_2_is_Eq :≡ λ {A}. λ a. λ {b b'}. λ e. \
                                                 Eq_U_intro'' (λ f : a = b. λ f' : a = b'. trans f e = f') \
                                                              (λ f : a = b. trans f e) \
                                                              (sorry _) \
                                                              (λ f : a = b'. trans f (symm e)) \
                                                              (sorry _)"],
                    },
                    DefInit {
                        sym: "Eq_Fun_nat : Π {A B : U}. Π {f g : A → B}. Π efg : f = g. Π {a a' : A}. Π ea : a = a'. \
                                           trans (efg a) (ap g ea) = trans' (ap f ea) (efg a')",
                        red: &["Eq_Fun_nat :≡ λ {A B f g}. apd {A} {λ a. f a = g a}"],
                    },
                    DefInit {
                        sym: "Eq_id_nat : Π {A : U}. Π {f : A → A}. Π ef : (Π a : A. f a = a). Π {a a' : A}. Π ea : a = a'. \
                                          trans (ef a) ea = trans' (ap f ea) (ef a')",
                        red: &["Eq_id_nat :≡ λ {A f}. Eq_Fun_nat {A} {A} {f} {id A}"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "DepEq : Π {A B : U}. A = B → A → B → U",
                    red: &["DepEq :≡ Eq_rel"],
                },
                defs: &[
                    DefInit {
                        sym: "DepEq_to : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. (a =[eAB] b) = (to eAB a = b)",
                        red: &["DepEq_to :≡ Eq_rel_to"],
                    },
                    DefInit {
                        sym: "DepEq_inv : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. (a =[eAB] b) = (a = inv eAB b)",
                        red: &["DepEq_inv :≡ Eq_rel_inv"],
                    },
                    DefInit {
                        sym: "DepEq_refl : Π {A : U}. Π a : A. a =[refl A] a",
                        red: &["DepEq_refl :≡ refl"],
                    },
                    DefInit {
                        sym: "DepEq_symm : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. a =[eAB] b → b =[symm eAB] a",
                        red: &["DepEq_symm :≡ λ {A B eAB a b}. id (a =[eAB] b)"],
                    },
                    DefInit {
                        sym: "DepEq_trans : Π {A B C : U}. Π {eAB : A = B}. Π {eBC : B = C}. Π {a : A}. Π {b : B}. Π {c : C}. a =[eAB] b → b =[eBC] c → a =[trans eAB eBC] c",
                        red: &["DepEq_trans :≡ λ {A B C eAB eBC a b c}. λ e f. sorry _"],
                    },
                    DefInit {
                        sym: "DepEq_trans' : Π {A B C : U}. Π {eAB : A = B}. Π {eBC : B = C}. Π {a : A}. Π {b : B}. Π {c : C}. a =[eAB] b → b =[eBC] c → a =[trans' eAB eBC] c",
                        red: &["DepEq_trans' :≡ λ {A B C eAB eBC a b c}. λ e f. sorry _"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "IsUnique : Π {A : U}. A → U",
                    red: &["IsUnique :≡ λ {A}. λ a. Π b : A. a = b"],
                },
                defs: &[
                    DefInit {
                        sym: "IsUnique_isProp : Π {A : U}. IsProp A → Π a : A. IsProp (IsUnique a)",
                        red: &["IsUnique_isProp :≡ λ {A}. λ h a. sorry _"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "IsProp : U → U",
                    red: &["IsProp :≡ λ A. Pi (IsUnique {A})"],
                },
                defs: &[
                    DefInit {
                        sym: "IsProp_to_IsSet : Π A : U. IsProp A → IsSet A",
                        red: &["IsProp_to_IsSet :≡ λ A h. sorry _"],
                    },
                    DefInit {
                        sym: "IsProp_isProp : Π A : U. IsProp (IsProp A)",
                        red: &["IsProp_isProp :≡ λ A. sorry _"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "IsSet : U → U",
                    red: &["IsSet :≡ λ A. Π a b : A. IsProp (a = b)"],
                },
                defs: &[
                    DefInit {
                        sym: "IsSet_isProp : Π A : U. IsProp (IsSet A)",
                        red: &["IsSet_isProp :≡ λ A. sorry _"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "IsContr : U → U",
                    red: &["IsContr :≡ λ A. Sigma (IsUnique {A})"],
                },
                defs: &[
                    DefInit {
                        sym: "IsContr_center : Π {A : U}. IsContr A → A",
                        red: &["IsContr_center :≡ λ {A}. Sigma_fst {A} {IsUnique {A}}"],
                    },
                    DefInit {
                        sym: "IsContr_unique : Π {A : U}. Π h : IsContr A. IsUnique (IsContr_center h)",
                        red: &["IsContr_unique :≡ λ {A}. Sigma_snd {A} {IsUnique {A}}"],
                    },
                    DefInit {
                        sym: "IsContr_to_IsProp : Π A : U. IsContr A → IsProp A",
                        red: &["IsContr_to_IsProp :≡ λ A h. \
                                                     λ a b : A. trans (symm (IsContr_unique h a)) \
                                                                      (IsContr_unique h b)"],
                    },
                    DefInit {
                        sym: "IsContr_isProp : Π A : U. IsProp (IsContr A)",
                        red: &["IsContr_isProp :≡ λ A. sorry _"],
                    },
                    DefInit {
                        sym: "IsContr_eq_Eq_Unit : Π A : U. IsContr A = (A = Unit)",
                        red: &["IsContr_eq_Eq_Unit :≡ λ A. sorry _"],
                    },
                ],
            },
            /*TypeInit {
                ctor: DefInit {
                    sym: "ContrSigma : Π {A : U}. (A → U) → U",
                    red: &["ContrSigma :≡ λ {A}. λ P. IsContr (Sigma P)"],
                },
                defs: &[
                    DefInit {
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
                    },
                    DefInit {
                        sym: "ContrSigma_fst : Π {A : U}. Π {P : A → U}. ContrSigma P → A",
                        red: &["ContrSigma_fst :≡ λ {A P}. λ h. Sigma_fst {A} {P} (IsContr_center h)"],
                    },
                    DefInit {
                        sym: "ContrSigma_snd : Π {A : U}. Π {P : A → U}. Π h : ContrSigma P. P (ContrSigma_fst h)",
                        red: &["ContrSigma_snd :≡ λ {A P}. λ h. Sigma_snd {A} {P} (IsContr_center h)"],
                    },
                    DefInit {
                        sym: "ContrSigma_unique_fst : Π {A : U}. Π {P : A → U}. Π h : ContrSigma P. Π a : A. P a → \
                                                      ContrSigma_fst h = a",
                        red: &["ContrSigma_unique_fst :≡ λ {A P}. λ h a b. \
                                                         Sigma_fst {ContrSigma_fst h = a} \
                                                                   {λ e : ContrSigma_fst h = a. ContrSigma_snd h =[ap P e] b} \
                                                                   (IsContr_unique h (Sigma_intro P a b))"],
                    },
                    DefInit {
                        sym: "ContrSigma_unique_snd : Π {A : U}. Π {P : A → U}. Π h : ContrSigma P. Π a : A. Π b : P a. \
                                                      ContrSigma_snd h =[ap P (ContrSigma_unique_fst h a b)] b",
                        red: &["ContrSigma_unique_snd :≡ λ {A P}. λ h a b. \
                                                         Sigma_snd {ContrSigma_fst h = a} \
                                                                   {λ e : ContrSigma_fst h = a. ContrSigma_snd h =[ap P e] b} \
                                                                   (IsContr_unique h (Sigma_intro P a b))"],
                    },
                    DefInit {
                        sym: "ContrSigma_isProp : Π {A : U}. Π P : A → U. IsProp (ContrSigma P)",
                        red: &["ContrSigma_isProp :≡ λ {A}. λ P. IsContr_isProp (Sigma P)"],
                    },
                    DefInit {
                        sym: "ContrSigma_Eq : Π {A : U}. Π a : A. ContrSigma (Eq a)",
                        red: &["ContrSigma_Eq :≡ λ {A}. λ a. \
                                                 ContrSigma_intro (Eq a) a (refl a) \
                                                                  (λ b : A. λ e : a = b. e) \
                                                                  (λ b : A. λ e : a = b. refl e)"],
                    },
                    DefInit {
                        sym: "ContrSigma_swap_Eq : Π {A : U}. Π a : A. ContrSigma ((Rel_swap (Eq {A})) a)",
                        red: &["ContrSigma_swap_Eq :≡ λ {A}. λ a. \
                                                      ContrSigma_intro ((Rel_swap (Eq {A})) a) a (refl a) \
                                                                       (λ b : A. λ e : b = a. symm e) \
                                                                       (λ b : A. λ e : b = a. refl (symm e))"],
                    },
                ],
            },*/
            TypeInit {
                ctor: DefInit {
                    sym: "IsFunRel : Π {A B : U}. (A → B → U) → U",
                    red: &[],
                },
                defs: &[
                    DefInit {
                        sym: "IsFunRel_intro : Π {A B : U}. Π R : A → B → U. Π f : A → B. R = Fun_to_Rel f → \
                                               IsFunRel R",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsFunRel_Eq : Π A : U. IsFunRel (Eq {A})",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsFunRel_swap_Eq : Π A : U. IsFunRel (Rel_swap (Eq {A}))",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsFunRel_comp_1 : Π {A B C : U}. Π {R : B → C → U}. IsFunRel R → Π f : A → B. \
                                                IsFunRel (Rel_comp_1 R f)",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsFunRel_comp_2 : Π {A B C : U}. Π e : B = C. Π {R : A → B → U}. IsFunRel R → \
                                                IsFunRel (Rel_comp_2 R (inv e))",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsFunRel_swapd_rel : Π A B : U. Π Q : A → B → U. \
                                                   IsFunRel (swapd_rel A B Q)",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsFunRel_swap_swapd_rel : Π A B : U. Π Q : A → B → U. \
                                                        IsFunRel (Rel_swap (swapd_rel A B Q))",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsFunRel_to : Π {A B : U}. Π {R : A → B → U}. IsFunRel R → A → B",
                        red: &[
                            "∀ {A B : U}. ∀ R : A → B → U. ∀ f : A → B. ∀ hf : R = Fun_to_Rel f. \
                             IsFunRel_to (IsFunRel_intro R f hf) :≡ f",
                            "∀ A : U. IsFunRel_to (IsFunRel_Eq A) :≡ id A",
                            "∀ A : U. IsFunRel_to (IsFunRel_swap_Eq A) :≡ id A",
                            "∀ {A B C : U}. ∀ {R : B → C → U}. ∀ h : IsFunRel R. ∀ f : A → B. \
                             IsFunRel_to (IsFunRel_comp_1 h f) :≡ comp (IsFunRel_to h) f",
                            "∀ {A B C : U}. ∀ e : B = C. ∀ {R : A → B → U}. ∀ h : IsFunRel R. \
                             IsFunRel_to (IsFunRel_comp_2 e h) :≡ comp (to e) (IsFunRel_to h)",
                            "∀ A B : U. ∀ Q : A → B → U. \
                             IsFunRel_to (IsFunRel_swapd_rel A B Q) :≡ swapd {A} {B} {Q}",
                            "∀ A B : U. ∀ Q : A → B → U. \
                             IsFunRel_to (IsFunRel_swap_swapd_rel A B Q) :≡ swapd {B} {A} {Rel_swap Q}",
                        ],
                    },
                    DefInit {
                        sym: "IsFunRel_eq : Π {A B : U}. Π {R : A → B → U}. Π h : IsFunRel R. \
                                            R = Fun_to_Rel (IsFunRel_to h)",
                        red: &[
                            "∀ {A B : U}. ∀ R : A → B → U. ∀ f : A → B. ∀ hf : R = Fun_to_Rel f. \
                             IsFunRel_eq (IsFunRel_intro R f hf) :≡ hf",
                            "∀ A : U. IsFunRel_eq (IsFunRel_Eq A) :≡ λ a b : A. refl (a = b)",
                            "∀ A : U. IsFunRel_eq (IsFunRel_swap_Eq A) :≡ λ a b : A. symm_is_Eq b a",
                            "∀ {A B C : U}. ∀ {R : B → C → U}. ∀ h : IsFunRel R. ∀ f : A → B. \
                             IsFunRel_eq (IsFunRel_comp_1 h f) :≡ λ a : A. λ c : C. (IsFunRel_eq h) (f a) c",
                            "∀ {A B C : U}. ∀ e : B = C. ∀ {R : A → B → U}. ∀ h : IsFunRel R. \
                             IsFunRel_eq (IsFunRel_comp_2 e h) :≡ λ a : A. λ c : C. \
                                                                  trans {U} {R a (inv e c)} {IsFunRel_to h a = inv e c} {to e (IsFunRel_to h a) = c} \
                                                                        ((IsFunRel_eq h) a (inv e c)) (symm (Eq_to_inv_eq e (IsFunRel_to h a) c))",
                            "∀ A B : U. ∀ Q : A → B → U. \
                             IsFunRel_eq (IsFunRel_swapd_rel A B Q) :≡ λ f : Pi2 Q. λ f' : Pi2 (Rel_swap Q). \
                                                                       swapd_is_Eq A B (λ a b. f a b ={Q a b} f' b a)",
                            "∀ A B : U. ∀ Q : A → B → U. \
                             IsFunRel_eq (IsFunRel_swap_swapd_rel A B Q) :≡ λ f' : Pi2 (Rel_swap Q). λ f : Pi2 Q. \
                                                                            apd (Pi2 {A} {B}) \
                                                                                {λ a : A. λ b : B. f a b ={Q a b} f' b a} \
                                                                                {λ a : A. λ b : B. f' b a ={Q a b} f a b} \
                                                                                (λ a : A. λ b : B. symm_is_Eq {Q a b} (f a b) (f' b a))",
                        ],
                    },
                    DefInit {
                        sym: "IsFunRel_inst : Π {A B : U}. Π {R : A → B → U}. Π h : IsFunRel R. Π a : A. \
                                              R a (IsFunRel_to h a)",
                        red: &["IsFunRel_inst :≡ λ {A B R}. λ h a. \
                                                 inv ((IsFunRel_eq h) a (IsFunRel_to h a)) \
                                                     (refl (IsFunRel_to h a))"],
                    },
                    DefInit {
                        sym: "IsFunRel_unique : Π {A B : U}. Π {R : A → B → U}. Π h : IsFunRel R. \
                                                Π a : A. Π b : B. R a b → \
                                                IsFunRel_to h a = b",
                        red: &["IsFunRel_unique :≡ λ {A B R}. λ h a b. to ((IsFunRel_eq h) a b)"],
                    },
                    DefInit {
                        // This shows that our version of equivalence is equivalent to the
                        // "bijective relation" variant in the HoTT book.
                        // TODO: The proof currently uses a strange reverse path induction. We
                        // should reduce it to the underlying application of `apd` once it is done,
                        // to see if it can be simplified that way.
                        sym: "IsFunRel_inst_unique : Π {A B : U}. Π {R : A → B → U}. Π h : IsFunRel R. \
                                                     Π a : A. Π b : B. Π hRab : R a b. \
                                                     IsFunRel_inst h a =[ap (R a) (IsFunRel_unique h a b hRab)] hRab",
                        red: &["IsFunRel_inst_unique :≡ λ {A B R}. λ h a b hRab. \
                                                        [h1 : inv ((IsFunRel_eq h) a b) (IsFunRel_unique h a b hRab) = hRab \
                                                            ⫽ inv_to {R a b} {IsFunRel_to h a = b} ((IsFunRel_eq h) a b) hRab] \
                                                        [h2 : ap (R a) (trans (symm (IsFunRel_unique h a b hRab)) \
                                                                       (IsFunRel_unique h a b hRab)) = \
                                                              refl (R a b)
                                                            ⫽ ap_ap (R a) (trans_1_symm (IsFunRel_unique h a b hRab))] \
                                                        [h3 : inv ((IsFunRel_eq h) a b) (IsFunRel_unique h a b hRab) \
                                                              =[ap (R a) (trans (symm (IsFunRel_unique h a b hRab)) \
                                                                                (IsFunRel_unique h a b hRab))] \
                                                              hRab \
                                                            ⫽ inv (ap_DepEq h2 (inv ((IsFunRel_eq h) a b) (IsFunRel_unique h a b hRab)) hRab) h1] \
                                                        substd_rl (λ b' : B. λ e : IsFunRel_to h a = b'. \
                                                                   inv ((IsFunRel_eq h) a b') e \
                                                                   =[ap (R a) (trans (symm e) (IsFunRel_unique h a b hRab))] \
                                                                   hRab) \
                                                                  (IsFunRel_unique h a b hRab) \
                                                                  h3"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "IsBijRel : Π {A B : U}. (A → B → U) → U",
                    red: &[],
                },
                defs: &[
                    DefInit {
                        sym: "IsBijRel_intro : Π {A B : U}. Π {R : A → B → U}. IsFunRel R → IsFunRel (Rel_swap R) → \
                                               IsBijRel R",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsBijRel_Eq : Π A : U. IsBijRel (Eq {A})",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsBijRel_swap : Π {A B : U}. Π {R : A → B → U}. IsBijRel R → IsBijRel (Rel_swap R)",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsBijRel_comp_1 : Π {A B C : U}. Π {R : B → C → U}. IsBijRel R → Π e : A = B. \
                                                IsBijRel (Rel_comp_1 R (to e))",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsBijRel_comp_2 : Π {A B C : U}. Π e : B = C. Π {R : A → B → U}. IsBijRel R → \
                                                IsBijRel (Rel_comp_2 R (inv e))",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsBijRel_to_isFunRel : Π {A B : U}. Π {R : A → B → U}. IsBijRel R → IsFunRel R",
                        red: &[
                            "∀ {A B : U}. ∀ {R : A → B → U}. ∀ hTo : IsFunRel R. ∀ hInv : IsFunRel (Rel_swap R). \
                             IsBijRel_to_isFunRel (IsBijRel_intro hTo hInv) :≡ hTo",
                            "∀ A : U. IsBijRel_to_isFunRel (IsBijRel_Eq A) :≡ IsFunRel_Eq A",
                            "∀ {A B : U}. ∀ {R : A → B → U}. ∀ h : IsBijRel R. \
                             IsBijRel_to_isFunRel (IsBijRel_swap h) :≡ IsBijRel_inv_isFunRel h",
                            "∀ {A B C : U}. ∀ {R : B → C → U}. ∀ h : IsBijRel R. ∀ e : A = B. \
                             IsBijRel_to_isFunRel (IsBijRel_comp_1 h e) :≡ IsFunRel_comp_1 (IsBijRel_to_isFunRel h) (to e)",
                            "∀ {A B C : U}. ∀ e : B = C. ∀ {R : A → B → U}. ∀ h : IsBijRel R. \
                             IsBijRel_to_isFunRel (IsBijRel_comp_2 e h) :≡ IsFunRel_comp_2 e (IsBijRel_to_isFunRel h)",
                        ],
                    },
                    DefInit {
                        sym: "IsBijRel_inv_isFunRel : Π {A B : U}. Π {R : A → B → U}. IsBijRel R → IsFunRel (Rel_swap R)",
                        red: &[
                            "∀ {A B : U}. ∀ {R : A → B → U}. ∀ hTo : IsFunRel R. ∀ hInv : IsFunRel (Rel_swap R). \
                             IsBijRel_inv_isFunRel (IsBijRel_intro hTo hInv) :≡ hInv",
                            "∀ A : U. IsBijRel_inv_isFunRel (IsBijRel_Eq A) :≡ IsFunRel_swap_Eq A",
                            "∀ {A B : U}. ∀ {R : A → B → U}. ∀ h : IsBijRel R. \
                             IsBijRel_inv_isFunRel (IsBijRel_swap h) :≡ IsBijRel_to_isFunRel h",
                            "∀ {A B C : U}. ∀ {R : B → C → U}. ∀ h : IsBijRel R. ∀ e : A = B. \
                             IsBijRel_inv_isFunRel (IsBijRel_comp_1 h e) :≡ IsFunRel_comp_2 (symm e) (IsBijRel_inv_isFunRel h)",
                            "∀ {A B C : U}. ∀ e : B = C. ∀ {R : A → B → U}. ∀ h : IsBijRel R. \
                             IsBijRel_inv_isFunRel (IsBijRel_comp_2 e h) :≡ IsFunRel_comp_1 (IsBijRel_inv_isFunRel h) (inv e)",
                        ],
                    },
                ],
            },
        ],
        &[
            DefInit {
                sym: "ap : Π {A B : U}. Π f : A → B. Π {a a' : A}. a = a' → f a = f a'",
                red: &[
                    // We could simply define `ap` as a special case of `apd`. However,
                    // non-dependent application generally yields much simpler terms, and it often
                    // appears in types, so we explicitly specify non-dependent variants of all
                    // cases here.
                    "∀ {A B : U}. ∀ f : A → B. ∀ a : A. ap f (refl a) :≡ refl (f a)",
                    // -- Type constructors --
                    "∀ {A : U}. ∀ a : A. ap (Eq a) :≡ trans_2_is_Eq a",
                    "∀ A : U. ap (Eq {A}) :≡ trans_1_is_Eq {A}",
                    // TODO
                    // -- Combinators --
                    "∀ A : U. ap (id A) :≡ λ {a a'}. λ e. e",
                    "∀ A : U. ∀ {B : U}. ∀ b : B. ap (const A b) :≡ λ {a a'}. λ e. refl b",
                    // Note: Due to the reduction rule of `trans'`, it is important that the second
                    // argument of `subst` becomes `refl` when `g` is constant on `A`, so that
                    // `ap` on function composition reduces nicely.
                    "∀ {A B C : U}. ∀ g : A → B → C. ∀ f : A → B. \
                     ap {A} {C} (subst {A} {const A B} {const A (const B C)} g f) :≡ λ {a a'}. λ e. trans' {C} {g a (f a)} {g a (f a')} {g a' (f a')} (ap (g a) (ap f e)) ((ap g e) (f a'))",
                    //"∀ {A : U}. ∀ {P : A → U}. ∀ {C : U}. ∀ g : (Π a : A. P a → C). ∀ f : Pi P. \
                    // ap {A} {C} (subst {A} {P} {λ a b. C} g f) :≡ λ {a a'}. λ e. trans {C} {g a (f a)} {g a' (f a)} {g a' (f a')} ((apd g e) (f a)) (ap (g a') (apd f e))",
                    // TODO other elimination functions
                ],
            },
            DefInit {
                sym: "ap_f_symm : Π {A B : U}. Π f : A → B. Π {a b : A}. Π e : a = b. \
                                  ap f (symm e) = symm (ap f e)",
                red: &["ap_f_symm :≡ sorry _"],
            },
            DefInit {
                sym: "ap_f_trans : Π {A B : U}. Π f : A → B. Π {a b c : A}. Π eab : a = b. Π ebc : b = c. \
                                   ap f (trans eab ebc) = trans (ap f eab) (ap f ebc)",
                red: &["ap_f_trans :≡ sorry _"],
            },
            DefInit {
                sym: "ap_subst_nat : Π {A B C : U}. Π g : A → B → C. Π f : A → B. Π {a a' : A}. Π e : a = a'. \
                                     ap {A} {C} (subst {A} {const A B} {const A (const B C)} g f) e = \
                                     trans {C} {g a (f a)} {g a' (f a)} {g a' (f a')} ((ap g e) (f a)) (ap (g a') (ap f e))",
                red: &["ap_subst_nat :≡ λ {A B C}. λ g f. λ {a a'}. λ e. \
                                        symm (Eq_Fun_nat {B} {C} {g a} {g a'} (ap g e) (ap f e))"],
            },
            DefInit {
                sym: "apd : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a a' : A}. Π e : a = a'. f a =[ap P e] f a'",
                red: &[
                    // See above.
                    "∀ A B : U. apd {A} {const A B} :≡ ap {A} {B}",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ a : A. apd f (refl a) :≡ DepEq_refl (f a)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ {Q : (Π a : A. P a → U)}. ∀ g : Pi2d Q. ∀ f : Pi P. \
                     apd (subst g f) :≡ λ {a a'}. λ e. sorry _",
                    // TODO
                ],
            },
            DefInit {
                sym: "apd_f_symm : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a b : A}. Π e : a = b. \
                                   apd f (symm e) =[ap_DepEq (ap_f_symm P e) (f b) (f a)] DepEq_symm (apd f e)",
                red: &["apd_f_symm :≡ sorry _"],
            },
            DefInit {
                sym: "apd_f_trans : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a b c : A}. Π eab : a = b. Π ebc : b = c. \
                                    apd f (trans eab ebc) =[ap_DepEq (ap_f_trans P eab ebc) (f a) (f c)] DepEq_trans (apd f eab) (apd f ebc)",
                red: &["apd_f_trans :≡ sorry _"],
            },
            DefInit {
                sym: "subst_lr : Π {A : U}. Π P : A → U. Π {a a' : A}. a = a' → P a → P a'",
                red: &["subst_lr :≡ λ {A}. λ P. λ {a a'}. λ e. to (ap P e)"],
            },
            DefInit {
                sym: "subst_rl : Π {A : U}. Π P : A → U. Π {a a' : A}. a = a' → P a' → P a",
                red: &["subst_rl :≡ λ {A}. λ P. λ {a a'}. λ e. inv (ap P e)"],
            },
            DefInit {
                sym: "ap_ap : Π {A B : U}. Π f : A → B. Π {a a' : A}. Π {e e' : a = a'}. \
                              e = e' → ap f e = ap f e'",
                red: &["ap_ap :≡ λ {A B}. λ f. λ {a a'}. ap (ap f {a} {a'})"],
            },
            DefInit {
                sym: "ap_symm : Π {A : U}. Π {a b : A}. Π {e e' : a = b}. e = e' → symm e = symm e'",
                red: &["ap_symm :≡ λ {A a b e e'}. λ he. ap (symm {A} {a} {b}) he"],
            },
            DefInit {
                sym: "ap_trans_1 : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π f : b = c. trans e f = trans e' f",
                red: &["ap_trans_1 :≡ λ {A a b c e e'}. λ he f. (ap (trans {A} {a} {b} {c}) he) f"],
            },
            DefInit {
                sym: "ap_trans'_1 : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π f : b = c. trans' e f = trans' e' f",
                red: &["ap_trans'_1 :≡ λ {A a b c e e'}. λ he f. (ap (trans' {A} {a} {b} {c}) he) f"],
            },
            DefInit {
                sym: "ap_trans_2 : Π {A : U}. Π {a b c : A}. Π e : a = b. Π {f f' : b = c}. f = f' → trans e f = trans e f'",
                red: &["ap_trans_2 :≡ λ {A a b c}. λ e. λ {f f'}. λ hf. ap (trans {A} {a} {b} {c} e) hf"],
            },
            DefInit {
                sym: "ap_trans'_2 : Π {A : U}. Π {a b c : A}. Π e : a = b. Π {f f' : b = c}. f = f' → trans' e f = trans' e f'",
                red: &["ap_trans'_2 :≡ λ {A a b c}. λ e. λ {f f'}. λ hf. ap (trans' {A} {a} {b} {c} e) hf"],
            },
            DefInit {
                sym: "ap_trans : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π {f f' : b = c}. f = f' → trans e f = trans e' f'",
                red: &["ap_trans :≡ λ {A a b c e e'}. λ he. λ {f f'}. λ hf. sorry _"],
            },
            DefInit {
                sym: "ap_trans' : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π {f f' : b = c}. f = f' → trans' e f = trans' e' f'",
                red: &["ap_trans' :≡ λ {A a b c e e'}. λ he. λ {f f'}. λ hf. sorry _"],
            },
            DefInit {
                sym: "ap_DepEq : Π {A B : U}. Π {eAB eAB' : A = B}. Π heAB : eAB = eAB'. Π a : A. Π b : B. \
                                 (a =[eAB] b) = (a =[eAB'] b)",
                red: &["ap_DepEq :≡ λ {A B eAB eAB'}. λ heAB a b. ap (λ e : A = B. a =[e] b) heAB"],
            },
            DefInit {
                sym: "apj : Π {A : U}. Π {a a' : A}. Π P : (Π b : A. a = b → U). Π e : a = a'. P a (refl a) = P a' e",
                red: &["apj :≡ λ {A a a'}. λ P e. sorry _"], // trans3 _ ((apd P e) e) _)
            },
            DefInit {
                sym: "substd_lr : Π {A : U}. Π {a a' : A}. Π P : (Π b : A. a = b → U). Π e : a = a'. P a (refl a) → P a' e",
                red: &["substd_lr :≡ λ {A a a'}. λ P e. to (apj P e)"],
            },
            DefInit {
                sym: "substd_rl : Π {A : U}. Π {a a' : A}. Π P : (Π b : A. a = b → U). Π e : a = a'. P a' e → P a (refl a)",
                red: &["substd_rl :≡ λ {A a a'}. λ P e. inv (apj P e)"],
            },
            DefInit {
                sym: "sorry : Π A : U. A", // TODO: remove once everything is filled
                red: &["∀ {A : U}. ∀ a : A. sorry (a = a) :≡ refl a"], // to reduce temporary failures
            },
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
    subst_idx: VarIndex,
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
            subst_idx: *constants.get("subst").unwrap(),
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

        let subst_cmb = mltt.get_constant("subst").unwrap();
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
            "subst {Pi {U} (const U {U} U)} {const (Pi {U} (const U {U} U)) {U} U} {const (Pi {U} (const U {U} U)) {Pi {U} (const U {U} U)} (const U {U} U)} (id (Pi {U} (const U {U} U))) (const (Pi {U} (const U {U} U)) {U} U)"
        );
        let app_u_cmb_type = app_u.get_type(&root_ctx)?;
        assert!(app_u_cmb_type.compare(&app_u_type, &mltt.get_root_context())?);

        id_fun.convert_to_combinators(&root_ctx, -1)?;
        assert_eq!(id_fun.print(&root_ctx), "id");

        let mut pi_type = pi.type_expr.clone();
        pi_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            pi_type.print(&root_ctx),
            "Pi {U} (subst {U} {λ {A : U}. (A → U) → U} {λ {A : U}. λ _ : (A → U) → U. U} (λ {A : U}. Pi {A → U}) (λ {A : U}. λ _ : A → U. U))"
        );

        let mut id_cmb_type = id_cmb.type_expr.clone();
        id_cmb_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            id_cmb_type.print(&root_ctx),
            "Pi {U} (subst {U} {λ A : U. A → U} {λ A : U. λ _ : A → U. U} (λ A : U. Pi {A}) (λ A : U. λ _ : A. A))"
        );
        assert_eq!(id_cmb_type.get_type(&root_ctx)?, univ);

        let mut const_cmb_type = const_cmb.type_expr.clone();
        const_cmb_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            const_cmb_type.print(&root_ctx),
            "Pi {U} (subst {U} {λ A : U. U → U} {λ A : U. λ _ : U → U. U} (λ A : U. Pi {U}) (λ A : U. λ {B : U}. B → A → B))"
        );
        assert_eq!(const_cmb_type.get_type(&root_ctx)?, univ);

        let mut subst_cmb_type = subst_cmb.type_expr.clone();
        subst_cmb_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            subst_cmb_type.print(&root_ctx),
            "Pi {U} (subst {U} {λ {A : U}. (A → U) → U} {λ {A : U}. λ _ : (A → U) → U. U} (λ {A : U}. Pi {A → U}) (λ {A : U}. λ {P : A → U}. Π {Q : (Π a : A. P a → U)}. Pi2d {A} {P} Q → (Π f : Pi {A} P. Π a : A. Q a (f a))))"
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
