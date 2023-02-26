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
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Pi : Π {A : U}. (A → U) → U",
                    red: &[],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "Pi_eq : Π {A : U}. Π {P P' : A → U}. P = P' → Pi P = Pi P'",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Fun_1_eq : Π {A A' : U}. Π eA : A = A'. Π B : U. (A → B) = (A' → B)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Pi_1_eq : Π {A A' : U}. Π eA : A = A'. Π P : A → U. Π P' : A' → U. \
                                        (Π {a : A}. Π {a' : A'}. a =[eA] a' → P a = P' a') → \
                                        Pi P = Pi P'",
                        red: &[],
                    }),
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
                        sym: "swapd_eq : Π {A B : U}. Π Q : A → B → U. \
                                         Pi2 Q = Pi2 (Rel_swap Q)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "swap_eq : Π A B C : U. (A → B → C) = (B → A → C)",
                        red: &["swap_eq :≡ λ A B C. swapd_eq (const A (const B C))"],
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
                        // We reduce the type `Eq {A}` for all specific types `A` except `U`, where
                        // we define introduction and elimination functions instead.
                        // We could define a specific type `Equiv` and reduce to that, but then e.g.
                        // `refl` would reduce to `Equiv_refl` but not further, leading to a lot of
                        // duplication because we need to match on `Equiv_refl` in addition whenever
                        // we really just want to match on `refl`.
                        "Eq {Unit} :≡ λ _ _. Unit",
                        "∀ {A : U}. ∀ P : A → U. Eq {Pi P} :≡ λ f g. Π a : A. f a = g a",
                        "∀ {A : U}. ∀ P : A → U. \
                         Eq {Sigma P} :≡ λ p q. Σ e_fst : Sigma_fst p = Sigma_fst q. \
                                                Sigma_snd p =[ap P e_fst] Sigma_snd q",
                        "∀ A B : U. Eq {A = B} :≡ λ e f. Eqd e = Eqd f",
                    ],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "Eq_U_intro : Π {A B : U}. Π f : A → B. Π g : B → A. \
                                           (Π a : A. Π b : B. (f a = b) = (a = g b)) → \
                                           A = B",
                        red: &[],
                    }),
                    // We treat `refl`, `symm`, and `trans` as (additional) constructors, which
                    // allows us to do many generic reductions -- essentially anything except
                    // cancellation. In general, if there is a conflict between some generic
                    // reduction and a concrete case of it, we try to keep the generic reduction
                    // and make the concrete case axiomatic instead.
                    ModuleInit::Def(DefInit {
                        sym: "refl : Π {A : U}. Π a : A. a = a",
                        red: &[
                            "refl {Unit} :≡ λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. refl {Pi P} :≡ λ f. λ a : A. refl (f a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             refl {Sigma P} :≡ \
                             λ p. Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst p. \
                                               Sigma_snd p =[ap P e_fst] Sigma_snd p) \
                                              (refl (Sigma_fst p)) \
                                              (refld (Sigma_snd p))",
                            "∀ A B : U. refl {A = B} :≡ λ e. refl (Eqd e)",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans : Π {A : U}. Π {a b c : A}. a = b → b = c → a = c",
                        red: &[
                            // Generic reductions.
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. trans (refl a) e :≡ e",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. trans e (refl b) :≡ e",
                            // Reductions for `mid`.
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. \
                             trans (symm (left e)) (right e) :≡ e",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. \
                             trans (symm (right e)) (left e) :≡ symm e",
                            // Definitions for each type.
                            "trans {Unit} :≡ λ {_ _ _}. λ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. \
                             trans {Pi P} :≡ λ {f g h}. λ efg egh. λ a : A. trans (efg a) (egh a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             trans {Sigma P} :≡ \
                             λ {p q r}. λ epq eqr. \
                             Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst r. \
                                          Sigma_snd p =[ap P e_fst] Sigma_snd r) \
                                         (trans (Sigma_fst epq) (Sigma_fst eqr)) \
                                         (transd {P (Sigma_fst p)} {P (Sigma_fst q)} {P (Sigma_fst r)} \
                                                      {ap P (Sigma_fst epq)} {ap P (Sigma_fst eqr)} \
                                                      {Sigma_snd p} {Sigma_snd q} {Sigma_snd r} \
                                                      (Sigma_snd epq) (Sigma_snd eqr))",
                            "∀ A B : U. trans {A = B} :≡ \
                                        λ {e f g}. trans {A → B → U} {Eqd e} {Eqd f} {Eqd g}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_1_eq : Π {A : U}. Π a : A. Π {b c : A}. b = c → \
                                           (a = b) = (a = c)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_2_eq : Π {A : U}. Π {a b : A}. a = b → Π c : A. \
                                           (a = c) = (b = c)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "symm : Π {A : U}. Π {a b : A}. a = b → b = a",
                        red: &[
                            // Generic reductions.
                            "∀ {A : U}. ∀ a : A. symm (refl a) :≡ refl a",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. \
                             symm (trans e f) :≡ trans (symm f) (symm e)",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. symm (symm e) :≡ e",
                            // Definitions for each type.
                            "symm {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. symm {Pi P} :≡ λ {f g}. λ e. λ a : A. symm (e a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             symm {Sigma P} :≡ \
                             λ {p q}. λ e. \
                             Sigma_intro (λ e_fst : Sigma_fst q = Sigma_fst p. \
                                          Sigma_snd q =[ap P e_fst] Sigma_snd p) \
                                         (symm (Sigma_fst e)) \
                                         (symmd {P (Sigma_fst p)} {P (Sigma_fst q)} \
                                                     {ap P (Sigma_fst e)} \
                                                     {Sigma_snd p} {Sigma_snd q} \
                                                     (Sigma_snd e))",
                            "∀ A B : U. symm {A = B} :≡ \
                                        λ {e f}. symm {A → B → U} {Eqd e} {Eqd f}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "symm_eq : Π {A : U}. Π a b : A. (a = b) = (b = a)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "to : Π {A B : U}. A = B → A → B",
                        red: &[
                            // Standard constructors.
                            "∀ {A B : U}. ∀ f : A → B. ∀ g : B → A. \
                             ∀ hfg : (Π a : A. Π b : B. (f a = b) = (a = g b)). \
                             to (Eq_U_intro f g hfg) :≡ f",
                            "∀ A : U. to (refl A) :≡ id A",
                            "∀ {A B C : U}. ∀ e : A = B. ∀ f : B = C. \
                             to (trans e f) :≡ comp (to f) (to e)",
                            "∀ {A B : U}. ∀ e : A = B. \
                             to (symm e) :≡ inv e",
                            // Special equivalences.
                            // These need to be defined axiomatically instead of via `Eq_U_intro`
                            // because their implementation is inherently recursive.
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             to {{Pi2 Q}} {{Pi2 (Rel_swap Q)}} (swapd_eq Q) :≡ \
                             swapd {A} {B} {Q}",
                            "∀ {A : U}. ∀ a : A. ∀ {b c : A}. ∀ f : b = c. \
                             to (trans_1_eq a f) :≡ λ e : a = b. trans e f",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. ∀ c : A. \
                             to (trans_2_eq e c) :≡ λ f : a = c. trans (symm e) f",
                            "∀ {A : U}. ∀ a b : A. \
                             to (symm_eq a b) :≡ symm {A} {a} {b}",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. ∀ g : a = c. \
                             to (trans_1_shift_eq e f g) :≡ trans_1_shift_lr {A} {a} {b} {c} {e} {f} {g}",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. ∀ g : a = c. \
                             to (trans_2_shift_eq e f g) :≡ trans_2_shift_lr {A} {a} {b} {c} {e} {f} {g}",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. ∀ f : b = a. \
                             to (symm_shift_eq e f) :≡ symm_shift_lr {A} {a} {b} {e} {f}",
                            "∀ {A : U}. ∀ {P P' : A → U}. ∀ eP : P = P'. \
                             to (Pi_eq eP) :≡ λ f a. to (eP a) (f a)",
                            "∀ {A A' : U}. ∀ eA : A = A'. ∀ B : U. \
                             to (Fun_1_eq eA B) :≡ λ f a'. f (inv eA a')",
                            "∀ {A A' : U}. ∀ eA : A = A'. ∀ P : A → U. ∀ P' : A' → U. \
                             ∀ hP : (Π {a : A}. Π {a' : A'}. a =[eA] a' → P a = P' a'). \
                             to (Pi_1_eq eA P P' hP) :≡ \
                             λ f a'. to (hP (Eqd_refl_inv eA a')) (f (inv eA a'))",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "inv : Π {A B : U}. A = B → B → A",
                        red: &[
                            // Standard constructors.
                            "∀ {A B : U}. ∀ f : A → B. ∀ g : B → A. \
                             ∀ hfg : (Π a : A. Π b : B. (f a = b) = (a = g b)). \
                             inv (Eq_U_intro f g hfg) :≡ g",
                            "∀ A : U. inv (refl A) :≡ id A",
                            "∀ {A B C : U}. ∀ e : A = B. ∀ f : B = C. \
                             inv (trans e f) :≡ comp (inv e) (inv f)",
                            "∀ {A B : U}. ∀ e : A = B. \
                             inv (symm e) :≡ to e",
                            // Special equivalences.
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             inv {{Pi2 Q}} {{Pi2 (Rel_swap Q)}} (swapd_eq Q) :≡ \
                             swapd {B} {A} {Rel_swap Q}",
                            "∀ {A : U}. ∀ a : A. ∀ {b c : A}. ∀ f : b = c. \
                             inv (trans_1_eq a f) :≡ λ e : a = c. trans e (symm f)",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. ∀ c : A. \
                             inv (trans_2_eq e c) :≡ λ f : b = c. trans e f",
                            "∀ {A : U}. ∀ a b : A. \
                             inv (symm_eq a b) :≡ symm {A} {b} {a}",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. ∀ g : a = c. \
                             inv (trans_1_shift_eq e f g) :≡ trans_1_shift_rl {A} {b} {a} {c} {f} {symm e} {g}",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. ∀ g : a = c. \
                             inv (trans_2_shift_eq e f g) :≡ trans_2_shift_rl {A} {a} {c} {b} {e} {g} {symm f}",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. ∀ f : b = a. \
                             inv (symm_shift_eq e f) :≡ symm_shift_rl {A} {a} {b} {e} {f}",
                            "∀ {A : U}. ∀ {P P' : A → U}. ∀ eP : P = P'. \
                             inv (Pi_eq eP) :≡ λ f' a. inv (eP a) (f' a)",
                            "∀ {A A' : U}. ∀ eA : A = A'. ∀ B : U. \
                             inv (Fun_1_eq eA B) :≡ λ f' a. f' (to eA a)",
                            "∀ {A A' : U}. ∀ eA : A = A'. ∀ P : A → U. ∀ P' : A' → U. \
                             ∀ hP : (Π {a : A}. Π {a' : A'}. a =[eA] a' → P a = P' a'). \
                             inv (Pi_1_eq eA P P' hP) :≡ \
                             λ f' a. inv (hP (Eqd_refl_to eA a)) (f' (to eA a))",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "to_inv_congr : Π {A B : U}. Π e : A = B. Π a : A. Π b : B. \
                                             (to e a = b) = (a = inv e b)",
                        red: &[
                            // Standard constructors.
                            "∀ {A B : U}. ∀ f : A → B. ∀ g : B → A. \
                             ∀ hfg : (Π a : A. Π b : B. (f a = b) = (a = g b)). \
                             to_inv_congr (Eq_U_intro f g hfg) :≡ hfg",
                            "∀ A : U. to_inv_congr (refl A) :≡ λ a b. refl (a = b)",
                            "∀ {A B C : U}. ∀ e : A = B. ∀ f : B = C. \
                             to_inv_congr (trans e f) :≡ \
                             λ a c. trans {U} {to f (to e a) = c} {to e a = inv f c} {a = inv e (inv f c)} \
                                          (to_inv_congr f (to e a) c) (to_inv_congr e a (inv f c))",
                            "∀ {A B : U}. ∀ e : A = B. \
                             to_inv_congr (symm e) :≡ inv_to_congr e",
                            // Special equivalences.
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             to_inv_congr {{Pi2 Q}} {{Pi2 (Rel_swap Q)}} (swapd_eq Q) :≡ \
                             λ f g. swapd_eq (λ b : B. λ a : A. f a b = g b a)",
                            "∀ {A : U}. ∀ a : A. ∀ {b c : A}. ∀ f : b = c. \
                             to_inv_congr (trans_1_eq a f) :≡ λ e g. trans_2_shift_eq e f g",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. ∀ c : A. \
                             to_inv_congr (trans_2_eq e c) :≡ λ f g. trans_1_shift_eq (symm e) f g",
                            "∀ {A : U}. ∀ a b : A. \
                             to_inv_congr (symm_eq a b) :≡ symm_shift_eq {A} {a} {b}",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. ∀ g : a = c. \
                             to_inv_congr (trans_1_shift_eq e f g) :≡ sorry _",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. ∀ g : a = c. \
                             to_inv_congr (trans_2_shift_eq e f g) :≡ sorry _",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. ∀ f : b = a. \
                             to_inv_congr (symm_shift_eq e f) :≡ sorry _",
                            // TODO: For the following three definitions, we should go via the
                            // midpoint instead.
                            "∀ {A : U}. ∀ {P P' : A → U}. ∀ eP : P = P'. \
                             to_inv_congr (Pi_eq eP) :≡ \
                             λ f f'. Pi_eq {A} {λ a. to (eP a) (f a) = f' a} \
                                               {λ a. f a = inv (eP a) (f' a)} \
                                           (λ a : A. to_inv_congr (eP a) (f a) (f' a))",
                            "∀ {A A' : U}. ∀ eA : A = A'. ∀ B : U. \
                             to_inv_congr (Fun_1_eq eA B) :≡ sorry _",
                            "∀ {A A' : U}. ∀ eA : A = A'. ∀ P : A → U. ∀ P' : A' → U. \
                             ∀ hP : (Π {a : A}. Π {a' : A'}. a =[eA] a' → P a = P' a'). \
                             to_inv_congr (Pi_1_eq eA P P' hP) :≡ sorry _",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "inv_to_congr : Π {A B : U}. Π e : A = B. Π b : B. Π a : A. \
                                             (inv e b = a) = (b = to e a)",
                        red: &[
                            // Standard constructors.
                            "∀ {A B : U}. ∀ f : A → B. ∀ g : B → A. \
                             ∀ hfg : (Π a : A. Π b : B. (f a = b) = (a = g b)). \
                             inv_to_congr (Eq_U_intro f g hfg) :≡ \
                             λ b a. trans3 {U} {g b = a} {a = g b} {f a = b} {b = f a} \
                                           (symm_eq (g b) a) \
                                           (symm (hfg a b)) \
                                           (symm_eq (f a) b)",
                            "∀ A : U. inv_to_congr (refl A) :≡ λ b a. refl (b = a)",
                            "∀ {A B C : U}. ∀ e : A = B. ∀ f : B = C. \
                             inv_to_congr (trans e f) :≡ \
                             λ c a. trans {U} {inv e (inv f c) = a} {inv f c = to e a} {c = to f (to e a)} \
                                          (inv_to_congr e (inv f c) a) (inv_to_congr f c (to e a))",
                            "∀ {A B : U}. ∀ e : A = B. \
                             inv_to_congr (symm e) :≡ to_inv_congr e",
                            // Special equivalences.
                            "∀ {A B : U}. ∀ Q : A → B → U. \
                             inv_to_congr {{Pi2 Q}} {{Pi2 (Rel_swap Q)}} (swapd_eq Q) :≡ \
                             λ g f. swapd_eq (λ a : A. λ b : B. g b a = f a b)",
                            "∀ {A : U}. ∀ a : A. ∀ {b c : A}. ∀ f : b = c. \
                             inv_to_congr (trans_1_eq a f) :≡ λ g e. trans_2_shift_eq g (symm f) e",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. ∀ c : A. \
                             inv_to_congr (trans_2_eq e c) :≡ λ f g. trans_1_shift_eq e f g",
                            "∀ {A : U}. ∀ a b : A. \
                             inv_to_congr (symm_eq a b) :≡ symm_shift_eq {A} {b} {a}",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. ∀ g : a = c. \
                             inv_to_congr (trans_1_shift_eq e f g) :≡ sorry _",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. ∀ g : a = c. \
                             inv_to_congr (trans_2_shift_eq e f g) :≡ sorry _",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. ∀ f : b = a. \
                             inv_to_congr (symm_shift_eq e f) :≡ sorry _",
                            "∀ {A : U}. ∀ {P P' : A → U}. ∀ eP : P = P'. \
                             inv_to_congr (Pi_eq eP) :≡  \
                             λ f' f. Pi_eq {A} {λ a. inv (eP a) (f' a) = f a} \
                                               {λ a. f' a = to (eP a) (f a)} \
                                           (λ a : A. inv_to_congr (eP a) (f' a) (f a))",
                            "∀ {A A' : U}. ∀ eA : A = A'. ∀ B : U. \
                             inv_to_congr (Fun_1_eq eA B) :≡ sorry _",
                            "∀ {A A' : U}. ∀ eA : A = A'. ∀ P : A → U. ∀ P' : A' → U. \
                             ∀ hP : (Π {a : A}. Π {a' : A'}. a =[eA] a' → P a = P' a'). \
                             inv_to_congr (Pi_1_eq eA P P' hP) :≡ sorry _",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "inv_to : Π {A B : U}. Π e : A = B. Π a : A. inv e (to e a) = a",
                        red: &["inv_to :≡ λ {A B}. λ e a. \
                                          inv (inv_to_congr e (to e a) a) (refl (to e a))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "to_inv : Π {A B : U}. Π e : A = B. Π b : B. to e (inv e b) = b",
                        red: &["to_inv :≡ λ {A B}. λ e b. \
                                          inv (to_inv_congr e (inv e b) b) (refl (inv e b))"],
                    }),
                    /*ModuleInit::Def(DefInit {
                        sym: "ReflRel_eq : Π {A : U}. Π R : A → A → U. \
                                           (Π {a b : A}. a = b → R a b) = (Π a : A. R a a)",
                        red: &["ReflRel_eq :≡ λ {A}. λ R. \
                                                    Eq_U_intro (λ h : (Π {a b : A}. a = b → R a b). \
                                                                 λ a : A. h (refl a)) \
                                                                (λ h' : (Π a : A. R a a). \
                                                                 λ {a b : A}. λ e : a = b. \
                                                                 ap_lr (R a) e (h' a)) \
                                                                (sorry3 _)"],
                        //                                          λ h : (Π {a b : A}. a = b → R a b). \
                        //                                          λ h' : (Π a : A. R a a). \
                        //                                          symm (ReflDepRel_eq (λ {a b : A}. _))
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "ReflDepRel_eq : Π {A : U}. Π R : (Π {a b : A}. a = b → U). \
                                              (Π {a b : A}. Π e : a = b. R e) = (Π a : A. R (refl a))",
                        red: &["ReflDepRel_eq :≡ λ {A}. λ R. \
                                                       Eq_U_intro (λ h : (Π {a b : A}. Π e : a = b. R {a} {b} e). \
                                                                    λ a : A. h (refl a)) \
                                                                   (λ h' : (Π a : A. R {a} {a} (refl a)). \
                                                                    λ {a b : A}. λ e : a = b. \
                                                                    apj_lr (R {a}) e (h' a)) \
                                                                   (sorry3 _)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "ReflRel_inv_eqd : Π {A B : U}. Π eAB : A = B. Π R : A → B → U. \
                                                (Π {a : A}. Π {b : B}. a =[eAB] b → R a b) = \
                                                (Π b : B. R (inv eAB b) b)",
                        red: &["ReflRel_inv_eqd :≡ λ {A B}. λ eAB R. \
                                                         Eq_U_intro (λ h : (Π {a : A}. Π {b : B}. a =[eAB] b → R a b). \
                                                                      λ b : B. h (Eqd_refl_inv eAB b)) \
                                                                     (λ h' : (Π b : B. R (inv eAB b) b). \
                                                                      λ {a : A}. λ {b : B}. λ e : a =[eAB] b. \
                                                                      ap_rl (λ a : A. R a b) (Eqd_as_inv_eq e) (h' b)) \
                                                                     (sorry3 _)"],
                    }),*/
                    ModuleInit::Def(DefInit {
                        sym: "trans_1_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans (symm e) e = refl b",
                        red: &["trans_1_symm :≡ λ {A a b}. λ e. trans_2_symm (symm e)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_2_symm : Π {A : U}. Π {a b : A}. Π e : a = b. trans e (symm e) = refl a",
                        red: &[
                            "trans_2_symm {U} :≡ Eqd_trans_2_symm",
                            "trans_2_symm {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. \
                             trans_2_symm {Pi P} :≡ λ {f g}. λ e. λ a : A. trans_2_symm (e a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             trans_2_symm {Sigma P} :≡ λ {p q}. λ e. sorry1 _",
                            "∀ A B : U. \
                             trans_2_symm {A = B} :≡ λ {e f}. trans_2_symm {A → B → U} {Eqd e} {Eqd f}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_assoc : Π {A : U}. Π {a b c d : A}. \
                                            Π e : a = b. Π f : b = c. Π g : c = d. \
                                            trans (trans e f) g = trans e (trans f g)",
                        red: &[
                            "trans_assoc {U} :≡ Eqd_trans_assoc",
                            "trans_assoc {Unit} :≡ λ {_ _ _ _}. λ _ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. \
                             trans_assoc {Pi P} :≡ λ {f g h i}. λ efg egh ehi. \
                                                   λ a : A. trans_assoc (efg a) (egh a) (ehi a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             trans_assoc {Sigma P} :≡ λ {p q r s}. λ epq eqr ers. sorry1 _",
                            "∀ A B : U. \
                             trans_assoc {A = B} :≡ \
                             λ {e f g h}. trans_assoc {A → B → U} {Eqd e} {Eqd f} {Eqd g} {Eqd h}",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3 : Π {A : U}. Π {a b c d : A}. a = b → b = c → c = d → a = d",
                        red: &["trans3 :≡ λ {A a b c d}. λ e f g. mid (trans_assoc e f g)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_12 : Π {A : U}. Π {a b c d : A}. \
                                         Π e : a = b. Π f : b = c. Π g : c = d. \
                                         trans3 e f g = trans (trans e f) g",
                        red: &["trans3_12 :≡ λ {A a b c d}. λ e f g. left (trans_assoc e f g)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_23 : Π {A : U}. Π {a b c d : A}. \
                                          Π e : a = b. Π f : b = c. Π g : c = d. \
                                          trans3 e f g = trans e (trans f g)",
                        red: &["trans3_23 :≡ λ {A a b c d}. λ e f g. right (trans_assoc e f g)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_1_symm : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. \
                                              trans3 (symm e) e f = f",
                        red: &["trans3_1_symm :≡ λ {A a b c}. λ e f. \
                                                 trans (trans3_12 (symm e) e f) \
                                                       (ap_trans_1 (trans_1_symm e) f)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_1_symm' : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. \
                                               trans (symm e) (trans e f) = f",
                        red: &["trans3_1_symm' :≡ λ {A a b c}. λ e f. \
                                                  trans (symm (trans_assoc (symm e) e f)) \
                                                        (ap_trans_1 (trans_1_symm e) f)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_3_symm : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. \
                                              trans3 e f (symm f) = e",
                        red: &["trans3_3_symm :≡ λ {A a b c}. λ e f. \
                                                 trans (trans3_23 e f (symm f)) \
                                                       (ap_trans_2 e (trans_2_symm f))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans3_3_symm' : Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. \
                                               trans (trans e f) (symm f) = e",
                        red: &["trans3_3_symm' :≡ λ {A a b c}. λ e f. \
                                                  trans (trans_assoc e f (symm f)) \
                                                        (ap_trans_2 e (trans_2_symm f))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_1_shift_lr : Π {A : U}. Π {a b c : A}. \
                                                 Π {e : a = b}. Π {f : b = c}. Π {g : a = c}. \
                                                 trans e f = g → f = trans (symm e) g",
                        red: &["trans_1_shift_lr :≡ λ {A a b c e f g}. λ h. \
                                                    symm (trans_1_shift_rl (symm h))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_1_shift_rl : Π {A : U}. Π {a b c : A}. \
                                                 Π {e : a = c}. Π {f : a = b}. Π {g : b = c}. \
                                                 e = trans f g → trans (symm f) e = g",
                        red: &["trans_1_shift_rl :≡ λ {A a b c e f g}. λ h. \
                                                    trans (ap_trans_2 (symm f) h) (trans3_1_symm' f g)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_1_shift_eq : Π {A : U}. Π {a b c : A}. \
                                                 Π e : a = b. Π f : b = c. Π g : a = c. \
                                                 (trans e f = g) = (f = trans (symm e) g)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_2_shift_lr : Π {A : U}. Π {a b c : A}. \
                                                 Π {e : a = b}. Π {f : b = c}. Π {g : a = c}. \
                                                 trans e f = g → e = trans g (symm f)",
                        red: &["trans_2_shift_lr :≡ λ {A a b c e f g}. λ h. \
                                                    symm (trans_2_shift_rl (symm h))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_2_shift_rl : Π {A : U}. Π {a b c : A}. \
                                                 Π {e : a = c}. Π {f : a = b}. Π {g : b = c}. \
                                                 e = trans f g → trans e (symm g) = f",
                        red: &["trans_2_shift_rl :≡ λ {A a b c e f g}. λ h. \
                                                    trans (ap_trans_1 h (symm g)) (trans3_3_symm' f g)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_2_shift_eq : Π {A : U}. Π {a b c : A}. \
                                                 Π e : a = b. Π f : b = c. Π g : a = c. \
                                                 (trans e f = g) = (e = trans g (symm f))",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_1_cancel : Π {A : U}. Π {a b c : A}. Π {e : a = b}. Π {f f' : b = c}. \
                                               trans e f = trans e f' → f = f'",
                        red: &["trans_1_cancel :≡ λ {A a b c e f f'}. λ h. \
                                                  trans (symm (trans3_1_symm' e f)) (trans_1_shift_rl h)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "trans_2_cancel : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. Π {f : b = c}. \
                                               trans e f = trans e' f → e = e'",
                        red: &["trans_2_cancel :≡ λ {A a b c e e' f}. λ h. \
                                                  trans (trans_2_shift_lr h) (trans3_3_symm' e' f)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "symm_shift_lr : Π {A : U}. Π {a b : A}. Π {e : a = b}. Π {f : b = a}. \
                                              symm e = f → e = symm f",
                        red: &["symm_shift_lr :≡ λ {A a b e f}. \
                                                 ap_symm {A} {b} {a} {symm e} {f}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "symm_shift_rl : Π {A : U}. Π {a b : A}. Π {e : a = b}. Π {f : b = a}. \
                                              e = symm f → symm e = f",
                        red: &["symm_shift_rl :≡ λ {A a b e f}. \
                                                 ap_symm {A} {a} {b} {e} {symm f}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "symm_shift_eq : Π {A : U}. Π {a b : A}. Π e : a = b. Π f : b = a. \
                                              (symm e = f) = (e = symm f)",
                        red: &[],
                    }),
                    ModuleInit::Def(DefInit {
                        // Given an equality between `a` and `b`, obtain an arbitrary value that
                        // is equal to `a` and `b` but not definitionally equal to a particular one
                        // of them, unless both are already definitionally equal (and their equality
                        // definitionally equal to `refl`). In other words, we obtain an arbitrary
                        // point on the path between `a` and `b`.
                        // The purpose of this definition is to avoid confluence problems stemming
                        // from the need to choose between two equally good alternatives.
                        sym: "mid : Π {A : U}. Π {a b : A}. a = b → A",
                        red: &[
                            // Generic reductions.
                            "∀ {A : U}. ∀ a : A. mid (refl a) :≡ a",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. mid (symm e) :≡ mid e",
                            // TODO: Make sure that this always holds.
                            "∀ {A B : U}. ∀ f : A → B. ∀ {a a' : A}. ∀ e : a = a'. \
                             mid (ap f e) :≡ f (mid e)",
                            // Reductions for specific types.
                            "mid {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. \
                             mid {Pi P} :≡ λ {f g}. λ e. λ a : A. mid (e a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             mid {Sigma P} :≡ \
                             λ {p q}. λ e. \
                             Sigma_intro P \
                                         (mid (Sigma_fst e)) \
                                         (midd {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} \
                                               {Sigma_snd p} {Sigma_snd q} (Sigma_snd e))",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "left : Π {A : U}. Π {a b : A}. Π e : a = b. mid e = a",
                        red: &[
                            // Generic reductions.
                            "∀ {A : U}. ∀ a : A. left (refl a) :≡ refl a",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. \
                             left (symm e) :≡ right e",
                            "∀ {A B : U}. ∀ f : A → B. ∀ {a a' : A}. ∀ e : a = a'. \
                             left (ap f e) :≡ ap f (left e)",
                            // Reductions for specific types.
                            "left {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. \
                             left {Pi P} :≡ λ {f g}. λ e. λ a : A. left (e a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             left {Sigma P} :≡ \
                             λ {p q}. λ e. \
                             Sigma_intro (λ e_fst : mid (Sigma_fst e) = Sigma_fst p. \
                                          midd {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} \
                                               {Sigma_snd p} {Sigma_snd q} (Sigma_snd e) \
                                          =[ap P e_fst] \
                                          Sigma_snd p) \
                                         (left (Sigma_fst e)) \
                                         (leftd {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} \
                                                {Sigma_snd p} {Sigma_snd q} (Sigma_snd e))",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "right : Π {A : U}. Π {a b : A}. Π e : a = b. mid e = b",
                        red: &[
                            // Generic reductions.
                            "∀ {A : U}. ∀ a : A. right (refl a) :≡ refl a",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. \
                             right (symm e) :≡ left e",
                            "∀ {A B : U}. ∀ f : A → B. ∀ {a a' : A}. ∀ e : a = a'. \
                             right (ap f e) :≡ ap f (right e)",
                            // Reductions for specific types.
                            "right {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. \
                             right {Pi P} :≡ λ {f g}. λ e. λ a : A. right (e a)",
                            "∀ {A : U}. ∀ P : A → U. \
                             right {Sigma P} :≡ \
                             λ {p q}. λ e. \
                             Sigma_intro (λ e_fst : mid (Sigma_fst e) = Sigma_fst q. \
                                          midd {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} \
                                               {Sigma_snd p} {Sigma_snd q} (Sigma_snd e) \
                                          =[ap P e_fst] \
                                          Sigma_snd q) \
                                         (right (Sigma_fst e)) \
                                         (rightd {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} \
                                                {Sigma_snd p} {Sigma_snd q} (Sigma_snd e))",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        // Can be used to prove something about `mid` without breaking the symmetry.
                        // (Obviously, every property that holds for `a` or `b` also holds for
                        // `mid e`, but using that fact usually requires a choice.)
                        sym: "mid_elim : Π {A : U}. Π {a b : A}. Π e : a = b. \
                                         Π P : A → U. Π ha : P a. Π hb : P b. ha =[ap P e] hb → \
                                         P (mid e)",
                        red: &["mid_elim :≡ λ {A a b}. λ e P ha hb. \
                                            midd {P a} {P b} {ap P e} {ha} {hb}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eq_Fun_nat : Π {A B : U}. Π {f g : A → B}. Π efg : f = g. \
                                           Π {a a' : A}. Π ea : a = a'. \
                                           trans (efg a) (ap g ea) = trans (ap f ea) (efg a')",
                        red: &["Eq_Fun_nat :≡ λ {A B f g}. apd {A} {λ a. f a = g a}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eq_id_nat : Π {A : U}. Π {f : A → A}. Π ef : (Π a : A. f a = a). \
                                          Π {a a' : A}. Π ea : a = a'. \
                                          trans (ef a) ea = trans (ap f ea) (ef a')",
                        red: &["Eq_id_nat :≡ λ {A f}. Eq_Fun_nat {A} {A} {f} {id A}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eq_Pi_nat : Π {A : U}. Π {P : A → U}. Π {f g : Pi P}. Π efg : f = g. \
                                          Π {a a' : A}. Π ea : a = a'. \
                                          transd2 (efg a) (apd g ea) = transd1 (apd f ea) (efg a')",
                        red: &["Eq_Pi_nat :≡ λ {A P f g}. sorry _"], // apd {A} {λ a. f a = g a}
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "congr : Π {A B : U}. Π {f g : A → B}. f = g → \
                                      Π {a a' : A}. a = a' → f a = g a'",
                        red: &["congr :≡ λ {A B f g}. λ efg. λ {a a'}. λ ea. \
                                         mid (Eq_Fun_nat efg ea)"],
                    }),
                    ModuleInit::Def(DefInit {
                        // TODO: We need this to be a definitional equality.
                        sym: "congr_assoc : Π {A B C : U}. Π {g g' : B → C}. Π eg : g = g'. \
                                            Π {f f' : A → B}. Π ef : f = f'. \
                                            Π {a a' : A}. Π ea : a = a'. \
                                            congr {A} {C} {comp g f} {comp g' f'} \
                                                  (congr (λ f : A → B. λ a : A. eg (f a)) ef) ea = \
                                            congr eg (congr ef ea)",
                        red: &["congr_assoc :≡ sorry _"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "congrd : Π {A : U}. Π {P : A → U}. Π {f g : Pi P}. f = g → \
                                       Π {a a' : A}. Π ea : a = a'. f a =[ap P ea] g a'",
                        red: &["congrd :≡ λ {A P f g}. λ efg. λ {a a'}. λ ea. \
                                          mid (Eq_Pi_nat efg ea)"],
                    }),
                ],
            },
            ModuleInit::Type {
                ctor: DefInit {
                    sym: "Eqd : Π {A B : U}. A = B → A → B → U",
                    red: &[
                        // We need to be careful which cases we reduce here.
                        // The result should always be a (possibly dependent) equality where
                        // the first argument appears on the left and the second argument
                        // appears on the right. In particular, letting `symm` swap
                        // the relation would break confluence, as swapping the relation
                        // only swaps the arguments without swapping the inner equality.
                        // The concept is quite similar to `mid`, and it is conceivable that we
                        // could define `Eqd e` as `mid (to_inv_congr e)` (see `Eqd_mid_eq`).
                        // However, the resulting terms turn out to be quite difficult to match on.
                        "∀ {A B : U}. ∀ f : A → B. ∀ g : B → A. \
                         ∀ hfg : (Π a : A. Π b : B. (f a = b) = (a = g b)). \
                         Eqd (Eq_U_intro f g hfg) :≡ \
                         mid {A → B → U} {λ a b. f a = b} {λ a b. a = g b} hfg",
                        "∀ A : U. Eqd (refl A) :≡ Eq {A}",
                        "∀ {A B : U}. ∀ Q : A → B → U. Eqd (swapd_eq Q) :≡ \
                         λ f f'. Π a : A. Π b : B. f a b ={Q a b} f' b a",
                        "∀ {A : U}. ∀ {a b c d : A}. ∀ e : a = b. ∀ f : c = d. \
                         Eqd (trans (trans_1_eq a f) (trans_2_eq e d)) :≡ \
                         λ e' : a = c. λ f' : b = d. trans e' f = trans e f'",
                        "∀ {A : U}. ∀ {a b c d : A}. ∀ e : a = b. ∀ f : c = d. \
                         Eqd (trans (trans_2_eq e c) (trans_1_eq b f)) :≡ \
                         λ e' : a = c. λ f' : b = d. trans e' f = trans e f'",
                        "∀ {A : U}. ∀ {P P' : A → U}. ∀ eP : P = P'. \
                         Eqd (Pi_eq eP) :≡ λ f f'. Π a : A. f a =[eP a] f' a",
                        "∀ {A A' : U}. ∀ eA : A = A'. ∀ B : U. \
                         Eqd (Fun_1_eq eA B) :≡ \
                         λ f f'. Π {a : A}. Π {a' : A'}. a =[eA] a' → f a = f' a'",
                        "∀ {A A' : U}. ∀ eA : A = A'. ∀ P : A → U. ∀ P' : A' → U. \
                         ∀ hP : (Π {a : A}. Π {a' : A'}. a =[eA] a' → P a = P' a'). \
                         Eqd (Pi_1_eq eA P P' hP) :≡ \
                         λ f f'. Π {a : A}. Π {a' : A'}. Π ea : a =[eA] a'. f a =[hP ea] f' a'",
                    ],
                },
                defs: &[
                    ModuleInit::Def(DefInit {
                        sym: "refld : Π {A : U}. Π a : A. a =[refl A] a",
                        red: &["refld :≡ refl"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "transd : Π {A B C : U}. Π {eAB : A = B}. Π {eBC : B = C}. \
                                       Π {a : A}. Π {b : B}. Π {c : C}. \
                                       a =[eAB] b → b =[eBC] c → a =[trans eAB eBC] c",
                        red: &[
                            // Generic reductions.
                            "∀ A : U. transd {A} {A} {A} {refl A} {refl A} :≡ trans {A}",
                            "∀ {A B : U}. ∀ {eAB : A = B}. ∀ {a : A}. ∀ {b : B}. ∀ e : a =[eAB] b. \
                             transd (refld a) e :≡ e",
                            "∀ {A B : U}. ∀ {eAB : A = B}. ∀ {a : A}. ∀ {b : B}. ∀ e : a =[eAB] b. \
                             transd e (refld b) :≡ e",
                            // Reductions for `midd`.
                            "∀ {A B : U}. ∀ {eAB : A = B}. ∀ {a : A}. ∀ {b : B}. ∀ e : a =[eAB] b. \
                             transd (symmd (leftd e)) (rightd e) :≡ e",
                            "∀ {A B : U}. ∀ {eAB : A = B}. ∀ {a : A}. ∀ {b : B}. ∀ e : a =[eAB] b. \
                             transd (symmd (rightd e)) (leftd e) :≡ symmd e",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "transd1 : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b b' : B}. \
                                        a =[eAB] b → b = b' → a =[eAB] b'",
                        red: &["transd1 :≡ λ {A B eAB}. \
                                           transd {A} {B} {B} {eAB} {refl B}"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "transd2 : Π {A B : U}. Π {eAB : A = B}. Π {a a' : A}. Π {b : B}. \
                                        a = a' → a' =[eAB] b → a =[eAB] b",
                        red: &["transd2 :≡ λ {A B eAB}. \
                                           transd {A} {A} {B} {refl A} {eAB}"],
                    }),
                    /*ModuleInit::Def(DefInit {
                        sym: "transd_assoc : Π {A B C D : U}. \
                                             Π {eAB : A = B}. Π {eBC : B = C}. Π {eCD : C = D}. \
                                             Π {a : A}. Π {b : B}. Π {c : C}. Π {d : D}. \
                                             Π e : a =[eAB] b. Π f : b =[eBC] c. Π g : c =[eCD] d. \
                                             transd (transd e f) g = \
                                             transd {A} {B} {D} {eAB} {trans eBC eCD} {a} {b} {d} \
                                                    e (transd f g)",
                        red: &["transd_assoc :≡ sorry _"],
                    }),*/
                    ModuleInit::Def(DefInit {
                        sym: "symmd : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. \
                                      a =[eAB] b → b =[symm eAB] a",
                        red: &[
                            "∀ A : U. symmd {A} {A} {refl A} :≡ symm {A}",
                            "∀ {A : U}. ∀ a : A. symmd (refld a) :≡ refld a",
                            "∀ {A B C : U}. ∀ {eAB : A = B}. ∀ {eBC : B = C}.
                             ∀ {a : A}. ∀ {b : B}. ∀ {c : C}. ∀ e : a =[eAB] b. ∀ f : b =[eBC] c. \
                             symmd (transd e f) :≡ transd (symmd f) (symmd e)",
                            "∀ {A B : U}. ∀ {eAB : A = B}. ∀ {a : A}. ∀ {b : B}. ∀ e : a =[eAB] b. \
                             symmd (symmd e) :≡ e",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_mid_eq : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. \
                                           (a =[eAB] b) = mid (to_inv_congr eAB a b)",
                        red: &["Eqd_mid_eq :≡ λ {A B}. λ eAB a b. sorry2 _"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_elim : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. Π P : U → U. \
                                         Π hTo : P (to eAB a = b). Π hInv : P (a = inv eAB b). \
                                         hTo =[ap P (to_inv_congr eAB a b)] hInv → P (a =[eAB] b)",
                        red: &["Eqd_elim :≡ λ {A B}. λ eAB a b P hTo hInv i. \
                                            ap_rl P (Eqd_mid_eq eAB a b) \
                                                  (mid_elim (to_inv_congr eAB a b) P hTo hInv i)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_to_eq_eq : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. \
                                             (a =[eAB] b) = (to eAB a = b)",
                        red: &["Eqd_to_eq_eq :≡ λ {A B}. λ eAB a b. \
                                                trans (Eqd_mid_eq eAB a b) \
                                                      (left (to_inv_congr eAB a b))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_inv_eq_eq : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. \
                                              (a =[eAB] b) = (a = inv eAB b)",
                        red: &["Eqd_inv_eq_eq :≡ λ {A B}. λ eAB a b. \
                                                 trans (Eqd_mid_eq eAB a b) \
                                                       (right (to_inv_congr eAB a b))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_as_to_eq : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. \
                                             a =[eAB] b → to eAB a = b",
                        red: &["Eqd_as_to_eq :≡ λ {A B eAB a b}. to (Eqd_to_eq_eq eAB a b)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_by_to_eq : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. \
                                             to eAB a = b → a =[eAB] b",
                        red: &["Eqd_by_to_eq :≡ λ {A B}. λ eAB a b. inv (Eqd_to_eq_eq eAB a b)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_as_inv_eq : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. \
                                              a =[eAB] b → a = inv eAB b",
                        red: &["Eqd_as_inv_eq :≡ λ {A B eAB a b}. to (Eqd_inv_eq_eq eAB a b)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_by_inv_eq : Π {A B : U}. Π eAB : A = B. Π a : A. Π b : B. \
                                              a = inv eAB b → a =[eAB] b",
                        red: &["Eqd_by_inv_eq :≡ λ {A B}. λ eAB a b. inv (Eqd_inv_eq_eq eAB a b)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_refl_to : Π {A B : U}. Π eAB : A = B. Π a : A. \
                                            a =[eAB] to eAB a",
                        red: &["Eqd_refl_to :≡ λ {A B}. λ eAB a. \
                                               Eqd_by_to_eq eAB a (to eAB a) (refl (to eAB a))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_refl_inv : Π {A B : U}. Π eAB : A = B. Π b : B. \
                                             inv eAB b =[eAB] b",
                        red: &["Eqd_refl_inv :≡ λ {A B}. λ eAB b. \
                                                Eqd_by_inv_eq eAB (inv eAB b) b (refl (inv eAB b))"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_trans_2_symm : Π {A B : U}. Π eAB : A = B. Π a a' : A. \
                                                 (a =[trans eAB (symm eAB)] a') = (a = a')",
                        red: &["Eqd_trans_2_symm :≡ λ {A B}. λ eAB a a'. \
                                                    Eqd_elim (trans eAB (symm eAB)) a a' \
                                                             (λ h : U. h = (a = a')) \
                                                             (trans_2_eq (inv_to eAB a) a') \
                                                             (trans_1_eq a (inv_to eAB a')) \
                                                             (sorry3 _)"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_trans_assoc : Π {A B C D : U}. \
                                                Π eAB : A = B. Π eBC : B = C. Π eCD : C = D. \
                                                Π a : A. Π d : D. \
                                                (a =[trans (trans eAB eBC) eCD] d) = \
                                                (a =[trans eAB (trans eBC eCD)] d)",
                        red: &["Eqd_trans_assoc :≡ λ {A B C D}. λ eAB eBC eCD a d. sorry3 _"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "Eqd_ap_symm : Π {A B : U}. Π eAB eAB' : A = B. Π a : A. Π b : B. \
                                            (a =[eAB] b) = (a =[eAB'] b) → \
                                            (b =[symm eAB] a) = (b =[symm eAB'] a)",
                        red: &["Eqd_ap_symm :≡ sorry5 _"],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "midd : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. \
                                     a =[eAB] b → mid eAB",
                        red: &[
                            "∀ A : U. midd {A} {A} {refl A} :≡ mid {A}",
                            "∀ {A : U}. ∀ a : A. midd (refld a) :≡ a",
                            "∀ {A B : U}. ∀ {eAB : A = B}. ∀ {a : A}. ∀ {b : B}. ∀ e : a =[eAB] b. \
                             midd (symmd e) :≡ midd {A} {B} {eAB} {a} {b} e",
                            "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ {a a' : A}. ∀ e : a = a'. \
                             midd (apd f e) :≡ f (mid e)",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "leftd : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. \
                                      Π e : a =[eAB] b. midd e =[left eAB] a",
                        red: &[
                            "∀ A : U. leftd {A} {A} {refl A} :≡ left {A}",
                            "∀ {A : U}. ∀ a : A. leftd (refld a) :≡ refld a",
                            "∀ {A B : U}. ∀ {eAB : A = B}. ∀ {a : A}. ∀ {b : B}. ∀ e : a =[eAB] b. \
                             leftd (symmd e) :≡ rightd e",
                            "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ {a a' : A}. ∀ e : a = a'. \
                             leftd (apd f e) :≡ apd f (left e)",
                        ],
                    }),
                    ModuleInit::Def(DefInit {
                        sym: "rightd : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. \
                                       Π e : a =[eAB] b. midd e =[right eAB] b",
                        red: &[
                            "∀ A : U. rightd {A} {A} {refl A} :≡ right {A}",
                            "∀ {A : U}. ∀ a : A. rightd (refld a) :≡ refld a",
                            "∀ {A B : U}. ∀ {eAB : A = B}. ∀ {a : A}. ∀ {b : B}. ∀ e : a =[eAB] b. \
                             rightd (symmd e) :≡ leftd e",
                            "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ {a a' : A}. ∀ e : a = a'. \
                             rightd (apd f e) :≡ apd f (right e)",
                        ],
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
                    // -- Generic reductions --
                    // TODO: Make symm and trans reduce as required for these to work.
                    "∀ {A B : U}. ∀ f : A → B. ∀ a : A. ap f (refl a) :≡ refl (f a)",
                    "∀ {A B : U}. ∀ f : A → B. ∀ {a b c : A}. ∀ eab : a = b. ∀ ebc : b = c. \
                     ap f (trans eab ebc) :≡ trans (ap f eab) (ap f ebc)",
                    "∀ {A B : U}. ∀ f : A → B. ∀ {a b : A}. ∀ e : a = b. \
                     ap f (symm e) :≡ symm (ap f e)",
                    // -- Type constructors --
                    "∀ A : U. ap (Pi {A}) :≡ Pi_eq {A}",
                    "∀ B : U. ap (λ A : U. A → B) :≡ λ {A A'}. λ eA. Fun_1_eq eA B",
                    "∀ {A : U}. ∀ P : A → U. ∀ B : U. \
                     ap (λ a : A. P a → B) :≡ λ {a a'}. λ ea. Fun_1_eq (ap P ea) B",
                    // TODO: Remove this specialization once it becomes unnecessary.
                    "∀ B C : U. ap (λ A : U. (A → B) → C) :≡ λ {A A'}. λ eA. \
                                                             Fun_1_eq {A → B} {A' → B} \
                                                                      (Fun_1_eq eA B) C",
                    "∀ {A : U}. ∀ a : A. ap (Eq a) :≡ trans_1_eq a",
                    "∀ A : U. ap (Eq {A}) :≡ trans_2_eq {A}",
                    "∀ {A B : U}. ∀ eAB : A = B. ∀ a : A. ap (Eqd eAB a) :≡ ap_Eqd_3 eAB a",
                    "∀ {A B : U}. ∀ eAB : A = B. ap (Eqd eAB) :≡ ap_Eqd_2 eAB",
                    "∀ {A B : U}. ap (Eqd {A} {B}) :≡ ap_Eqd {A} {B}",
                    // TODO
                    // -- Combinators --
                    "∀ A : U. ap (id A) :≡ λ {a a'}. λ e. e",
                    "∀ A : U. ∀ {B : U}. ∀ b : B. ap (const A b) :≡ λ {a a'}. λ e. refl b",
                    "∀ A B : U. ap (const A {B}) :≡ λ {b b'}. λ e. λ a : A. e",
                    "∀ {A B C : U}. ∀ g : B → C. ∀ f : A → B. ap (subst (const A g) f) :≡ ap_comp g f",
                    "∀ {A B C : U}. ∀ g : A → B → C. ∀ f : A → B. ap (subst g f) :≡ ap_subst g f",
                    "∀ {A B C : U}. ∀ g : B → C. ap (subst (const A g)) :≡ λ {f f'}. λ e. λ a : A. ap g (e a)",
                    "∀ {A B C : U}. ∀ g : A → B → C. ap (subst g) :≡ λ {f f'}. λ e. λ a : A. ap (g a) (e a)",
                    "∀ A B C : U. ap (subst {A} {B} {C}) :≡ λ {g g'}. λ e. λ f : A → B. λ a : A. e a (f a)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ {C : U}. ∀ g : (Π a : A. P a → C). ∀ f : Pi P. \
                     ap {A} {C} (substd {A} {P} {{λ a. const (P a) C}} g f) :≡ ap_substd g f",
                    "∀ {A B : U}. ∀ {Q : A → U}. ∀ g : (Π a : A. B → Q a). \
                     ap {A → B} {Pi Q} (substd {A} {const A B} {{λ a. const B (Q a)}} g) :≡ \
                     λ {f f'}. λ e. λ a : A. ap (g a) (e a)",
                    // -- Other functions --
                    "∀ {A B : U}. ∀ f : A → B. ∀ a a' : A. ap (ap f {a} {a'}) :≡ ap_ap f {a} {a'}",
                    "∀ {A : U}. ∀ a b : A. ap (symm {A} {a} {b}) :≡ ap_symm {A} {a} {b}",
                    "∀ {A : U}. ∀ a b c : A. ∀ e : a = b. ap (trans {A} {a} {b} {c} e) :≡ ap_trans_2 {A} {a} {b} {c} e",
                    "∀ {A : U}. ∀ a b c : A. ap (trans {A} {a} {b} {c}) :≡ ap_trans_1 {A} {a} {b} {c}",
                    // TODO lots more
                ],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_Eqd : Π {A B : U}. Π {eAB eAB' : A = B}. Π heAB : eAB = eAB'. Π a : A. Π b : B. \
                               (a =[eAB] b) = (a =[eAB'] b)",
                red: &["ap_Eqd :≡ λ {A B eAB eAB'}. λ heAB a b. sorry4 _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_Eqd_2 : Π {A B : U}. Π eAB : A = B. Π {a a' : A}. Π ea : a = a'. Π b : B. \
                                 (a =[eAB] b) = (a' =[eAB] b)",
                red: &["ap_Eqd_2 :≡ λ {A B}. λ eAB. λ {a a'}. λ ea b. sorry4 _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_Eqd_3 : Π {A B : U}. Π eAB : A = B. Π a : A. Π {b b' : B}. Π eb : b = b'. \
                                 (a =[eAB] b) = (a =[eAB] b')",
                red: &["ap_Eqd_3 :≡ λ {A B}. λ eAB a. λ {b b'}. λ eb. sorry4 _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_comp : Π {A B C : U}. Π g : B → C. Π f : A → B. Π {a a' : A}. Π e : a = a'. \
                                comp g f a = comp g f a'",
                red: &["ap_comp :≡ λ {A B C}. λ g f. λ {a a'}. λ e. ap g (ap f e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_subst : Π {A B C : U}. Π g : A → B → C. Π f : A → B. Π {a a' : A}. Π e : a = a'. \
                                 subst g f a = subst g f a'",
                red: &["ap_subst :≡ λ {A B C}. λ g f. λ {a a'}. λ e. ap2 g e (ap f e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_substd : Π {A : U}. Π {P : A → U}. Π {C : U}. \
                                  Π g : (Π a : A. P a → C). Π f : Pi P. Π {a a' : A}. Π e : a = a'. \
                                  substd {A} {P} {λ a. const (P a) C} g f a = \
                                  substd {A} {P} {λ a. const (P a) C} g f a'",
                red: &["ap_substd :≡ λ {A P C}. λ g f. λ {a a'}. λ e. ap2d g e (apd f e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_ap : Π {A B : U}. Π f : A → B. Π {a a' : A}. Π {e e' : a = a'}. \
                              e = e' → ap f e = ap f e'",
                red: &["ap_ap :≡ λ {A B}. λ f. λ {a a'}. sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_trans_1 : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π f : b = c. \
                                   trans e f = trans e' f",
                red: &["ap_trans_1 :≡ λ {A a b c e e'}. λ he f. sorry5 _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_trans_2 : Π {A : U}. Π {a b c : A}. Π e : a = b. Π {f f' : b = c}. f = f' → \
                                   trans e f = trans e f'",
                red: &["ap_trans_2 :≡ λ {A a b c}. λ e. λ {f f'}. λ hf. sorry5 _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_trans : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π {f f' : b = c}. f = f' → \
                                 trans e f = trans e' f'",
                red: &["ap_trans :≡ λ {A a b c e e'}. λ he. λ {f f'}. λ hf. sorry5 _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_symm : Π {A : U}. Π {a b : A}. Π {e e' : a = b}. e = e' → symm e = symm e'",
                red: &[
                    "ap_symm {U} :≡ λ {A B eAB eAB'}. λ h. \
                                    λ b : B. λ a : A. Eqd_ap_symm eAB eAB' a b (h a b)",
                    "ap_symm {Unit} :≡ λ {_ _ _ _}. λ _. unit",
                    "∀ {A : U}. ∀ P : A → U. \
                     ap_symm {Pi P} :≡ λ {f g e e'}. λ h. \
                                       λ a : A. ap_symm {P a} {f a} {g a} {e a} {e' a} (h a)",
                    "∀ {A : U}. ∀ P : A → U. \
                     ap_symm {Sigma P} :≡ λ {p q e e'}. λ h. sorry5 _",
                    "∀ A B : U. \
                     ap_symm {A = B} :≡ λ {e f}. ap_symm {A → B → U} {Eqd e} {Eqd f}",
                ],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_to : Π {A B : U}. Π eAB : A = B. Π {a a' : A}. a = a' → to eAB a = to eAB a'",
                red: &["ap_to :≡ λ {A B}. λ eAB. λ {a a'}. λ ea. sorry4 _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_inv : Π {A B : U}. Π eAB : A = B. Π {b b' : B}. b = b' → inv eAB b = inv eAB b'",
                red: &["ap_inv :≡ λ {A B}. λ eAB. λ {b b'}. λ eb. sorry4 _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap2 : Π {A B C : U}. Π f : A → B → C. \
                            Π {a a' : A}. a = a' → Π {b b' : B}. b = b' → f a b = f a' b'",
                red: &["ap2 :≡ λ {A B C}. λ f. λ {a a'}. λ ea. λ {b b'}. λ eb. \
                               trans ((ap f ea) b) (ap (f a') eb)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap2' : Π {A B C : U}. Π f : A → B → C. \
                             Π {a a' : A}. a = a' → Π {b b' : B}. b = b' → f a b = f a' b'",
                red: &["ap2' :≡ λ {A B C}. λ f. λ {a a'}. λ ea. λ {b b'}. λ eb. \
                                trans (ap (f a) eb) ((ap f ea) b')"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap2_nat : Π {A B C : U}. Π f : A → B → C. \
                                Π {a a' : A}. Π ea : a = a'. Π {b b' : B}. Π eb : b = b'.
                                ap2 f ea eb = ap2' f ea eb",
                red: &["ap2_nat :≡ λ {A B C}. λ f. λ {a a'}. λ ea. λ {b b'}. λ eb. \
                                   Eq_Fun_nat (ap f ea) eb"],
            }),
            // TODO: Replace ap2 with this.
            // (Not possible yet because apd instance for trans_2_eq is missing.)
            ModuleInit::Def(DefInit {
                sym: "ap2'' : Π {A B C : U}. Π f : A → B → C. \
                              Π {a a' : A}. a = a' → Π {b b' : B}. b = b' → f a b = f a' b'",
                red: &["ap2'' :≡ λ {A B C}. λ f. λ {a a'}. λ ea. λ {b b'}. λ eb. \
                                 congr (ap f ea) eb"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap2d : Π {A : U}. Π {P : A → U}. Π {C : U}. Π f : (Π a : A. P a → C). \
                             Π {a a' : A}. Π ea : a = a'. \
                             Π {b : P a}. Π {b' : P a'}. b =[ap P ea] b' → \
                             f a b = f a' b'",
                red: &["ap2d :≡ λ {A P C}. λ f. λ {a a'}. λ ea. λ {b b'}. λ eb. \
                                sorry _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apd : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a a' : A}. Π e : a = a'. f a =[ap P e] f a'",
                red: &[
                    "∀ A B : U. apd {A} {const A B} :≡ ap {A} {B}", // See comment at `ap`.
                    // -- Generic reductions --
                    // TODO: Make symm and trans reduce as required for these to work.
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ a : A. \
                     apd f (refl a) :≡ refld (f a)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ {a b c : A}. ∀ eab : a = b. ∀ ebc : b = c. \
                     apd f (trans eab ebc) :≡ transd (apd f eab) (apd f ebc)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ {a b : A}. ∀ e : a = b. \
                     apd f (symm e) :≡ symmd (apd f e)",
                    // -- Type constructors --
                    "apd Pi :≡ Pi_1_eq",
                    // TODO
                    // -- Combinators --
                    "∀ {A B : U}. ∀ {Q : B → U}. ∀ g : Pi Q. ∀ f : A → B. \
                     apd {A} {{λ a. Q (f a)}} (substd {A} {const A B} {const A Q} (const A g) f) :≡ \
                     apd_compd g f",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ {Q : (Π a : A. P a → U)}. ∀ g : Pi2d Q. ∀ f : Pi P. \
                     apd {A} {{λ a. Q a (f a)}} (substd g f) :≡ sorry7 _",
                    /*"∀ {A B : U}. ∀ {Q : B → U}. ∀ g : Pi Q. \
                     apd {A → B} {{λ f. Π a : A. Q (f a)}} (substd {A} {const A B} {const A Q} (const A g)) :≡ \
                     λ {f f'}. λ e. λ a : A. apd g (e a)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ {Q : (Π a : A. P a → U)}. ∀ g : Pi2d Q. \
                     apd {Pi P} {{λ f. Π a : A. Q a (f a)}} (substd g) :≡ λ {f f'}. λ e. λ a : A. apd (g a) (e a)",
                    "∀ {A : U}. ∀ P : A → U. ∀ Q : (Π a : A. P a → U). apd (substd {A} {P} {Q}) :≡ \
                     λ {g g'}. λ e. λ f : Pi P. λ a : A. e a (f a)",*/
                    // TODO
                    // -- Other functions --
                    "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. apd (trans_2_eq e) :≡ sorry _"
                    // TODO
                ],
            }),
            ModuleInit::Def(DefInit {
                sym: "apd_compd : Π {A B : U}. Π {Q : B → U}. Π g : Pi Q. Π f : A → B. \
                                  Π {a a' : A}. Π e : a = a'. \
                                  compd g f a =[ap Q (ap f e)] compd g f a'",
                red: &["apd_compd :≡ λ {A B Q}. λ g f. λ {a a'}. λ e. apd g (ap f e)"],
            }),
            /*ModuleInit::Def(DefInit {
                sym: "apd_substd : Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. \
                                   Π g : Pi2d Q. Π f : Pi P. Π {a a' : A}. Π e : a = a'. \
                                   substd g f a =[] substd g f a'",
                red: &["apd_substd :≡ λ {A P Q}. λ g f. λ {a a'}. λ e. sorry _"],
            }),*/
            ModuleInit::Def(DefInit {
                sym: "apd2 : Π {A B : U}. Π {Q : A → B → U}. Π f : Pi2 Q. \
                             Π {a a' : A}. Π ea : a = a'. Π {b b' : B}. Π eb : b = b'. \
                             f a b =[ap2 Q ea eb] f a' b'",
                red: &["apd2 :≡ λ {A B Q}. λ f. λ {a a'}. λ ea. λ {b b'}. λ eb. \
                                sorry _"], // congrd (apd f ea) eb
            }),
            ModuleInit::Def(DefInit {
                sym: "apd2d : Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. Π f : Pi2d Q. \
                              Π {a a' : A}. Π ea : a = a'. \
                              Π {b : P a}. Π {b' : P a'}. Π eb : b =[ap P ea] b'. \
                              f a b =[ap2d Q ea eb] f a' b'",
                red: &["apd2d :≡ λ {A P Q}. λ f. λ {a a'}. λ ea. λ {b b'}. λ eb. \
                                 sorry _"], // congrd (apd f ea) eb
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_lr : Π {A : U}. Π P : A → U. Π {a a' : A}. a = a' → P a → P a'",
                red: &["ap_lr :≡ λ {A}. λ P. λ {a a'}. λ e. to (ap P e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ap_rl : Π {A : U}. Π P : A → U. Π {a a' : A}. a = a' → P a' → P a",
                red: &["ap_rl :≡ λ {A}. λ P. λ {a a'}. λ e. inv (ap P e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "ape : Π {A B : U}. Π e : A = B. Π a a' : A. (a = a') = (to e a = to e a')",
                red: &["ape :≡ λ {A B}. λ e a a'. sorry8 _"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apj : Π {A : U}. Π {a a' : A}. Π P : (Π {b : A}. a = b → U). Π e : a = a'. \
                            P (refl a) = P e",
                red: &["apj :≡ λ {A a a'}. λ P e. \
                               [h1 : Π {ea : a = a}. Π {ea' : a = a'}. ea =[trans_1_eq a e] ea' → \
                                     P {a} ea = P {a'} ea' \
                                   ⫽ apd P e] \
                               [h2 : refl a =[trans_1_eq a e] e \
                                   ⫽ Eqd_by_to_eq (trans_1_eq a e) (refl a) e (refl e)] \
                               h1 h2"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apj_lr : Π {A : U}. Π {a a' : A}. Π P : (Π {b : A}. a = b → U). Π e : a = a'. \
                               P (refl a) → P e",
                red: &["apj_lr :≡ λ {A a a'}. λ P e. to (apj P e)"],
            }),
            ModuleInit::Def(DefInit {
                sym: "apj_rl : Π {A : U}. Π {b b' : A}. Π P : (Π {a : A}. a = b' → U). Π e : b = b'. \
                               P (symm (refl b')) → P e",
                red: &["apj_rl :≡ λ {A b b'}. λ P e. \
                                  apj_lr (λ {a : A}. λ eab : b' = a. P {a} (symm eab)) (symm e)"],
            }),
            // TODO: remove once everything is filled
            ModuleInit::Def(DefInit {
                sym: "sorry : Π A : U. A",
                red: &[],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry1 : Π A : U. A",
                red: &[],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry2 : Π A : U. A",
                red: &[],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry3 : Π A : U. A",
                red: &[],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry4 : Π A : U. A",
                red: &[],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry5 : Π A : U. A",
                red: &[],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry6 : Π A : U. A",
                red: &[],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry7 : Π A : U. A",
                red: &[],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry8 : Π A : U. A",
                red: &[],
            }),
            ModuleInit::Def(DefInit {
                sym: "sorry9 : Π A : U. A",
                red: &[],
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
    eqd_idx: VarIndex,
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
            eqd_idx: *constants.get("Eqd").unwrap(),
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
            match_all: false,
        };
        let prop_arg = Arg {
            expr: prop,
            implicit: false,
            match_all: false,
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
            match_all: false,
        };
        let codomain_arg = Arg {
            expr: codomain,
            implicit: true,
            match_all: false,
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
            match_all: false,
        };
        let prop1_arg = Arg {
            expr: prop1,
            implicit: true,
            match_all: false,
        };
        let rel2_arg = Arg {
            expr: rel2,
            implicit: true,
            match_all: false,
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
            match_all: false,
        };
        let left_arg = Arg {
            expr: left,
            implicit: false,
            match_all: false,
        };
        let right_arg = Arg {
            expr: right,
            implicit: false,
            match_all: false,
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
            match_all: false,
        };
        let right_domain_arg = Arg {
            expr: right_domain,
            implicit: true,
            match_all: false,
        };
        let domain_eq_arg = Arg {
            expr: domain_eq,
            implicit: false,
            match_all: false,
        };
        let left_arg = Arg {
            expr: left,
            implicit: false,
            match_all: false,
        };
        let right_arg = Arg {
            expr: right,
            implicit: false,
            match_all: false,
        };
        Ok(Expr::multi_app(
            Expr::var(self.eqd_idx),
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
        4
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

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

        let pi = &mltt.get_constant("Pi").unwrap().param;
        assert_eq!(pi.type_expr.print(&root_ctx), "Π {A : U}. (A → U) → U");

        let id_cmb = &mltt.get_constant("id").unwrap().param;
        assert_eq!(id_cmb.type_expr.print(&root_ctx), "Π A : U. A → A");

        let const_cmb = &mltt.get_constant("const").unwrap().param;
        assert_eq!(
            const_cmb.type_expr.print(&root_ctx),
            "Π A : U. Π {B : U}. B → A → B"
        );

        let subst_cmb = &mltt.get_constant("substd").unwrap().param;
        assert_eq!(
            subst_cmb.type_expr.print(&root_ctx),
            "Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. \
             Pi2d {A} {P} Q → (Π f : Pi {A} P. Π a : A. Q a (f a))"
        );

        let refl = &mltt.get_constant("refl").unwrap().param;
        assert_eq!(
            refl.type_expr.print(&root_ctx),
            "Π {A : U}. Π a : A. a ={A} a"
        );

        let symm = &mltt.get_constant("symm").unwrap().param;
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
        let mut app_u_type = app_u.get_type(&root_ctx)?;
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
        let pair_fst_fun_reduced = pair_fst_fun.reduce_all(&root_ctx)?;
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
            "substd {Pi {U} (const U {U} U)} \
                    {const (Pi {U} (const U {U} U)) {U} U} \
                    {const (Pi {U} (const U {U} U)) {Pi {U} (const U {U} U)} (const U {U} U)} \
                    (id (Pi {U} (const U {U} U))) \
                    (const (Pi {U} (const U {U} U)) {U} U)"
        );
        assert!(app_u.has_type(&mut app_u_type, &mltt.get_root_context())?);

        id_fun.convert_to_combinators(&root_ctx, -1)?;
        assert_eq!(id_fun.print(&root_ctx), "id");

        let mut pi_type = pi.type_expr.clone();
        pi_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            pi_type.print(&root_ctx),
            "Pi {U} (substd {U} {λ {A : U}. (A → U) → U} {λ {A : U}. λ _ : (A → U) → U. U} \
                            (λ {A : U}. Pi {A → U}) (λ {A : U}. λ _ : A → U. U))"
        );

        let mut id_cmb_type = id_cmb.type_expr.clone();
        id_cmb_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            id_cmb_type.print(&root_ctx),
            "Pi {U} (substd {U} {λ A : U. A → U} {λ A : U. λ _ : A → U. U} \
                            (λ A : U. Pi {A}) (λ A : U. λ _ : A. A))"
        );
        assert_eq!(id_cmb_type.get_type(&root_ctx)?, univ);

        let mut const_cmb_type = const_cmb.type_expr.clone();
        const_cmb_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            const_cmb_type.print(&root_ctx),
            "Pi {U} (substd {U} {λ A : U. U → U} {λ A : U. λ _ : U → U. U} \
                            (λ A : U. Pi {U}) (λ A : U. λ {B : U}. B → A → B))"
        );
        assert_eq!(const_cmb_type.get_type(&root_ctx)?, univ);

        let mut subst_cmb_type = subst_cmb.type_expr.clone();
        subst_cmb_type.convert_to_combinators(&root_ctx, 2)?;
        assert_eq!(
            subst_cmb_type.print(&root_ctx),
            "Pi {U} (substd {U} {λ {A : U}. (A → U) → U} {λ {A : U}. λ _ : (A → U) → U. U} \
                            (λ {A : U}. Pi {A → U}) \
                            (λ {A : U}. λ {P : A → U}. \
                             Π {Q : (Π a : A. P a → U)}. Pi2d {A} {P} Q → (Π f : Pi {A} P. Π a : A. Q a (f a))))"
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

    /*#[test]
    fn test_confluence_related_reductions() -> Result<()> {
        let mltt = get_mltt();
        let root_ctx = mltt.get_root_context();

        let mut congr_assoc_left = mltt.parse_expr(
            "λ {A B C : U}. λ {g g' : B → C}. λ eg : g = g'. \
             λ {f f' : A → B}. λ ef : f = f'. \
             λ {a a' : A}. λ ea : a = a'. \
             congr {A} {C} {comp g f} {comp g' f'} \
                   (congr (λ f : A → B. λ a : A. eg (f a)) ef) ea",
        )?;
        congr_assoc_left.reduce_all(&root_ctx)?;
        assert_eq!(congr_assoc_left.print(&root_ctx), "TODO");

        Ok(())
    }*/

    #[test]
    fn test_example_reductions() -> Result<()> {
        let mut mltt = get_mltt();

        mltt.add_definition("PointedType", mltt.parse_expr("Σ A : U. A")?)?;

        let root_ctx = mltt.get_root_context();
        let mut pointed_type_eq = mltt.parse_expr("λ A B : PointedType. A = B")?;
        pointed_type_eq.reduce_all(&root_ctx)?;
        assert_eq!(
            pointed_type_eq.print(&root_ctx),
            "λ A : (Σ A : U. A). λ B : (Σ A' : U. A'). \
             Σ e_fst : Sigma_fst A = Sigma_fst B. Sigma_snd A =[e_fst] Sigma_snd B"
        );

        mltt.add_definition("TypeWithFun", mltt.parse_expr("Σ A : U. A → A")?)?;

        let root_ctx = mltt.get_root_context();
        let mut type_with_fun = mltt.parse_expr("λ A B : TypeWithFun. A = B")?;
        type_with_fun.reduce_all(&root_ctx)?;
        //assert_eq!(type_with_fun.print(&root_ctx), "TODO");

        mltt.add_definition("Magma", mltt.parse_expr("Σ A : U. A → A → A")?)?;

        let root_ctx = mltt.get_root_context();
        let mut magma_eq = mltt.parse_expr("λ A B : Magma. A = B")?;
        magma_eq.reduce_all(&root_ctx)?;
        //assert_eq!(magma_eq.print(&root_ctx), "TODO");

        Ok(())
    }

    // TODO: check equality of variable names in defs
    // TODO: fix implicit arguments before printing
    // TODO: check that `ap`/`apd` is defined for every irreducible function
    // TODO: test confluence (in general, or just of all concrete terms)
}
