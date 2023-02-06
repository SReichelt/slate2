use std::collections::HashMap;

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
                    sym: "Eq : Π {A : U}. A → A → U",
                    // We could directly reduce equality to type-dependent equivalence, but instead
                    // we introduce a separate type `Equiv` for the latter. This gives us a little
                    // more flexibility in reduction rules, and it significantly improves
                    // performance because matching against equality is much simpler than matching
                    // against a reducible equivalence (as we currently just eagerly reduce all
                    // types when checking for definitional equality).
                    // The downside is that we have to insert some explicit conversions, of course.
                    red: &[],
                },
                defs: &[
                    // We treat `Equiv_to_Eq`, `refl`, `symm`, and `trans` as constructors, which
                    // we only reduce in cases where that is compatible with all other operations.
                    // This way, we "remember" the structure of equalities until they are destructed
                    // by `Eq_to_Equiv`.
                    DefInit {
                        sym: "Equiv_to_Eq : Π {A : U}. Π {a b : A}. Equiv a b → a = b",
                        red: &[],
                    },
                    DefInit {
                        sym: "refl : Π {A : U}. Π a : A. a = a",
                        red: &[],
                    },
                    DefInit {
                        sym: "symm : Π {A : U}. Π {a b : A}. a = b → b = a",
                        red: &[
                            "∀ {A : U}. ∀ a : A. symm (refl a) :≡ refl a",
                        ],
                    },
                    DefInit {
                        sym: "trans : Π {A : U}. Π {a b c : A}. a = b → b = c → a = c",
                        red: &[
                            // We are only allowed to eliminate `refl` in the first argument due to
                            // the definition of `mid`.
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. trans (refl a) e :≡ e",
                        ],
                    },
                    // "Remembering" the structure of equalities lets us query an "inflection point"
                    // such that the part left of that point has a "forward" (or indeterminate)
                    // direction and the part right of it has a "backward" direction (i.e. it is
                    // surrounded by `symm`).
                    // This has two advantages:
                    // * Dependent equality (aka pathover) becomes symmetric. In addition to making
                    //   things simpler, this produces terms with fewer inverses, e.g. the standard
                    //   definitions of isomorphisms.
                    // * Even though there is a certain asymmetry in equality of types (due to
                    //   `Equiv` being defined like in HoTT), many instances of `symm (symm e)`
                    //   essentially reduce to `e` -- not literally, but as arguments to `mid`,
                    //   `left`, or `right`.
                    // Note how the reduction rules are given four each of the four constructors
                    // above.
                    DefInit {
                        sym: "mid : Π {A : U}. Π {a b : A}. a = b → A",
                        red: &[
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : Equiv a b. mid (Equiv_to_Eq e) :≡ Equiv_mid e",
                            "∀ {A : U}. ∀ a : A. mid (refl a) :≡ a",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. mid (symm e) :≡ mid e",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. mid (trans e f) :≡ mid f",
                        ],
                    },
                    DefInit {
                        sym: "left : Π {A : U}. Π {a b : A}. Π e : a = b. a = mid e",
                        red: &[
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : Equiv a b. left (Equiv_to_Eq e) :≡ Equiv_to_Eq (Equiv_left e)",
                            "∀ {A : U}. ∀ a : A. left (refl a) :≡ refl a",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. left (symm e) :≡ right e",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. left (trans e f) :≡ trans e (left f)",
                        ],
                    },
                    DefInit {
                        sym: "right : Π {A : U}. Π {a b : A}. Π e : a = b. b = mid e",
                        red: &[
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : Equiv a b. right (Equiv_to_Eq e) :≡ Equiv_to_Eq (Equiv_right e)",
                            "∀ {A : U}. ∀ a : A. right (refl a) :≡ refl a",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. right (symm e) :≡ left e",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. right (trans e f) :≡ right f",
                        ],
                    },
                    DefInit {
                        sym: "trans_left_right: Π {A : U}. Π {a b : A}. Π e : a = b. trans (left e) (symm (right e)) = e",
                        red: &[
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : Equiv a b. trans_left_right (Equiv_to_Eq e) :≡ Equiv_to_Eq (Equiv_trans_left_right e)",
                            "∀ {A : U}. ∀ a : A. trans_left_right (refl a) :≡ refl (refl a)",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. trans_left_right (symm e) :≡ trans (symm (symm_trans_symm (left e) (right e))) (ap_symm (trans_left_right e))",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. trans_left_right (trans e f) :≡ trans (symm (assoc e (left f) (symm (right f)))) (ap_trans_2 e (trans_left_right f))",
                        ],
                    },
                    DefInit {
                        sym: "trans_right_left: Π {A : U}. Π {a b : A}. Π e : a = b. trans (right e) (symm (left e)) = symm e",
                        red: &["trans_right_left :≡ λ {A a b}. λ e. trans_left_right (symm e)"],
                    },
                    DefInit {
                        sym: "Eq_to_Equiv : Π {A : U}. Π {a b : A}. a = b → Equiv a b",
                        red: &[
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : Equiv a b. Eq_to_Equiv (Equiv_to_Eq e) :≡ e",
                            "∀ {A : U}. ∀ a : A. Eq_to_Equiv (refl a) :≡ Equiv_refl a",
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : a = b. Eq_to_Equiv (symm e) :≡ Equiv_symm (Eq_to_Equiv e)",
                            "∀ {A : U}. ∀ {a b c : A}. ∀ e : a = b. ∀ f : b = c. Eq_to_Equiv (trans e f) :≡ Equiv_trans (Eq_to_Equiv e) (Eq_to_Equiv f)",
                        ],
                    },
                    DefInit {
                        sym: "to : Π {A B : U}. A = B → A → B",
                        red: &["to :≡ λ {A B}. λ e. Equiv_U_to (Eq_to_Equiv e)"],
                    },
                    DefInit {
                        sym: "inv : Π {A B : U}. A = B → B → A",
                        red: &["inv :≡ λ {A B}. λ e. Equiv_U_inv (Eq_to_Equiv e)"],
                    },
                    DefInit {
                        sym: "symm_symm: Π {A : U}. Π {a b : A}. Π e : a = b. symm (symm e) = e",
                        red: &["symm_symm :≡ λ {A a b}. λ e. Equiv_to_Eq (Equiv_symm_symm (Eq_to_Equiv e))"],
                    },
                    DefInit {
                        sym: "symm_trans: Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : b = c. symm (trans e f) = trans (symm f) (symm e)",
                        red: &["symm_trans :≡ λ {A a b c}. λ e f. Equiv_to_Eq (Equiv_symm_trans (Eq_to_Equiv e) (Eq_to_Equiv f))"],
                    },
                    DefInit {
                        sym: "symm_trans_symm: Π {A : U}. Π {a b c : A}. Π e : a = b. Π f : c = b. symm (trans e (symm f)) = trans f (symm e)",
                        red: &["symm_trans_symm :≡ λ {A a b c}. λ e f. sorry _"],
                    },
                    DefInit {
                        sym: "trans_refl: Π {A : U}. Π {a b : A}. Π e : a = b. trans e (refl b) = e",
                        red: &["trans_refl :≡ λ {A a b}. λ e. Equiv_to_Eq (Equiv_trans_refl (Eq_to_Equiv e))"],
                    },
                    DefInit {
                        sym: "trans_e_symm: Π {A : U}. Π {a b : A}. Π e : a = b. trans e (symm e) = refl a",
                        red: &["trans_e_symm :≡ λ {A a b}. λ e. Equiv_to_Eq (Equiv_trans_e_symm (Eq_to_Equiv e))"],
                    },
                    DefInit {
                        sym: "trans_symm_e: Π {A : U}. Π {a b : A}. Π e : a = b. trans (symm e) e = refl b",
                        red: &["trans_symm_e :≡ λ {A a b}. λ e. Equiv_to_Eq (Equiv_trans_symm_e (Eq_to_Equiv e))"],
                    },
                    DefInit {
                        sym: "trans3 : Π {A : U}. Π {a b c d : A}. a = b → b = c → c = d → a = d",
                        red: &["trans3 :≡ λ {A a b c d}. λ e f g. trans e (trans f g)"],
                    },
                    DefInit {
                        sym: "trans3' : Π {A : U}. Π {a b c d : A}. a = b → b = c → c = d → a = d",
                        red: &["trans3' :≡ λ {A a b c d}. λ e f g. trans (trans e f) g"],
                    },
                    DefInit {
                        sym: "assoc: Π {A : U}. Π {a b c d : A}. Π e : a = b. Π f : b = c. Π g : c = d. trans3 e f g = trans3' e f g",
                        red: &["assoc :≡ λ {A a b c d}. λ e f g. Equiv_to_Eq (Equiv_assoc (Eq_to_Equiv e) (Eq_to_Equiv f) (Eq_to_Equiv g))"],
                    },
                    DefInit {
                        sym: "inv_to : Π {A B : U}. Π e : A = B. Π a : A. inv e (to e a) = a",
                        red: &["inv_to :≡ λ {A B}. λ e. Equiv_U_inv_to (Eq_to_Equiv e)"],
                    },
                    DefInit {
                        sym: "to_inv : Π {A B : U}. Π e : A = B. Π b : B. to e (inv e b) = b",
                        red: &["to_inv :≡ λ {A B}. λ e. Equiv_U_to_inv (Eq_to_Equiv e)"],
                    },
                    DefInit {
                        sym: "to_right_left : Π {A B : U}. Π e : A = B. Π a : A. inv (right e) (to (left e) a) = to e a",
                        red: &["to_right_left :≡ λ {A B}. λ e. Eq_to_Equiv (ap (to {A} {B}) (trans_left_right e))"],
                    },
                    DefInit {
                        sym: "inv_left_right : Π {A B : U}. Π e : A = B. Π b : B. inv (left e) (to (right e) b) = inv e b",
                        red: &["inv_left_right :≡ λ {A B}. λ e. Eq_to_Equiv (ap (inv {A} {B}) (trans_left_right e))"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "DepEq : Π {A B : U}. A = B → A → B → U",
                    red: &["DepEq :≡ λ {A B}. λ eAB a b. to (left eAB) a = to (right eAB) b"],
                },
                defs: &[
                    DefInit {
                        // TODO: We should write this as a chain of invertible operations.
                        sym: "DepEq_to : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. a =[eAB] b → to eAB a = b",
                        red: &["DepEq_to :≡ λ {A B eAB a b}. λ e. trans3 (symm (to_right_left eAB a)) (ap (inv (right eAB)) e) (inv_to (right eAB) b)"],
                    },
                    DefInit {
                        sym: "DepEq_inv : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. a =[eAB] b → a = inv eAB b",
                        red: &["DepEq_inv :≡ λ {A B eAB a b}. λ e. trans3 (symm (inv_to (left eAB) a)) (ap (inv (left eAB)) e) (inv_left_right eAB b)"],
                    },
                    DefInit {
                        sym: "DepEq_from_to : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. to eAB a = b → a =[eAB] b",
                        red: &["DepEq_from_to :≡ λ {A B eAB a b}. λ e. sorry _"],
                    },
                    DefInit {
                        sym: "DepEq_from_inv : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. a = inv eAB b → a =[eAB] b",
                        red: &["DepEq_from_inv :≡ λ {A B eAB a b}. λ e. sorry _"],
                    },
                    DefInit {
                        sym: "DepEq_refl : Π {A : U}. Π a : A. a =[refl A] a",
                        red: &["DepEq_refl :≡ refl"],
                    },
                    DefInit {
                        sym: "DepEq_symm : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. a =[eAB] b → b =[symm eAB] a",
                        red: &["DepEq_symm :≡ λ {A B eAB a b}. symm {mid eAB} {to (left eAB) a} {to (right eAB) b}"],
                    },
                    DefInit {
                        sym: "DepEq_trans : Π {A B C : U}. Π {eAB : A = B}. Π {eBC : B = C}. Π {a : A}. Π {b : B}. Π {c : C}. a =[eAB] b → b =[eBC] c → a =[trans eAB eBC] c",
                        red: &["DepEq_trans :≡ λ {A B C eAB eBC a b c}. λ e. trans {mid eBC} {to (left eBC) (to eAB a)} {to (left eBC) b} {to (right eBC) c} (ap (to (left eBC)) (DepEq_to e))"],
                    },
                    DefInit {
                        sym: "DepEq_mid : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. a =[eAB] b → mid eAB",
                        red: &["DepEq_mid :≡ λ {A B eAB a b}. mid {mid eAB} {to (left eAB) a} {to (right eAB) b}"],
                    },
                    DefInit {
                        sym: "DepEq_left_to : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. Π e : a =[eAB] b. to (left eAB) a = DepEq_mid e",
                        red: &["DepEq_left_to :≡ λ {A B eAB a b}. left {mid eAB} {to (left eAB) a} {to (right eAB) b}"],
                    },
                    DefInit {
                        sym: "DepEq_left : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. Π e : a =[eAB] b. a =[left eAB] DepEq_mid e",
                        red: &["DepEq_left :≡ λ {A B eAB a b}. λ e. DepEq_from_to (DepEq_left_to e)"],
                    },
                    DefInit {
                        sym: "DepEq_right_to : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. Π e : a =[eAB] b. to (right eAB) b = DepEq_mid e",
                        red: &["DepEq_right_to :≡ λ {A B eAB a b}. right {mid eAB} {to (left eAB) a} {to (right eAB) b}"],
                    },
                    DefInit {
                        sym: "DepEq_right : Π {A B : U}. Π {eAB : A = B}. Π {a : A}. Π {b : B}. Π e : a =[eAB] b. b =[right eAB] DepEq_mid e",
                        red: &["DepEq_right :≡ λ {A B eAB a b}. λ e. DepEq_from_to (DepEq_right_to e)"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "Equiv : Π {A : U}. A → A → U",
                    red: &[
                        "Equiv {U} :≡ λ A B. Sigma (IsEquiv {A} {B})",
                        "Equiv {Unit} :≡ λ _ _. Unit",
                        "∀ {A : U}. ∀ P : A → U. Equiv {Pi P} :≡ λ f g. Π a : A. f a = g a",
                        "∀ {A : U}. ∀ P : A → U. Equiv {Sigma P} :≡ λ p q. Σ e_fst : Sigma_fst p = Sigma_fst q. Sigma_snd p =[ap P e_fst] Sigma_snd q",
                        "∀ {A : U}. ∀ a b : A. Equiv {a = b} :≡ λ e f. Eq_to_Equiv e = Eq_to_Equiv f",
                        "∀ {A B : U}. ∀ f : A → B. Equiv {IsEquiv f} :≡ λ _ _. Unit",
                    ],
                },
                defs: &[
                    DefInit {
                        sym: "Equiv_refl : Π {A : U}. Π a : A. Equiv a a",
                        red: &[
                            "Equiv_refl {U} :≡ λ A. Sigma_intro (IsEquiv {A} {A}) (id A) (IsEquiv_refl A)",
                            "Equiv_refl {Unit} :≡ λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. Equiv_refl {Pi P} :≡ λ f. λ a : A. refl (f a)",
                            "∀ {A : U}. ∀ P : A → U. Equiv_refl {Sigma P} :≡ λ p. Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst p. Sigma_snd p =[ap P e_fst] Sigma_snd p) (refl (Sigma_fst p)) (DepEq_refl (Sigma_snd p))",
                            "∀ {A : U}. ∀ a b : A. Equiv_refl {a = b} :≡ λ e. refl (Eq_to_Equiv e)",
                            "∀ {A B : U}. ∀ f : A → B. Equiv_refl {IsEquiv f} :≡ λ _. unit",
                        ],
                    },
                    DefInit {
                        sym: "Equiv_symm : Π {A : U}. Π {a b : A}. Equiv a b → Equiv b a",
                        red: &[
                            "∀ {A : U}. ∀ a : A. Equiv_symm (Equiv_refl a) :≡ Equiv_refl a",
                            "Equiv_symm {Unit} :≡ λ {_ _}. λ _. unit",
                            "Equiv_symm {U} :≡ λ {A B}. λ e. Sigma_intro (IsEquiv {B} {A}) (Equiv_U_inv e) (IsEquiv_symm (Sigma_snd e))",
                            "∀ {A : U}. ∀ P : A → U. Equiv_symm {Pi P} :≡ λ {f g}. λ e. λ a : A. symm (e a)",
                            "∀ {A : U}. ∀ P : A → U. Equiv_symm {Sigma P} :≡ λ {p q}. λ e. Sigma_intro (λ e_fst : Sigma_fst q = Sigma_fst p. Sigma_snd q =[ap P e_fst] Sigma_snd p) (symm {A} {Sigma_fst p} {Sigma_fst q} (Sigma_fst e)) (DepEq_symm {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} {Sigma_snd p} {Sigma_snd q} (Sigma_snd e))",
                            "∀ {A : U}. ∀ a b : A. Equiv_symm {a = b} :≡ λ {e f}. symm {Equiv a b} {Eq_to_Equiv e} {Eq_to_Equiv f}",
                            "∀ {A B : U}. ∀ f : A → B. Equiv_symm {IsEquiv f} :≡ λ {_ _}. λ _. unit",
                        ],
                    },
                    DefInit {
                        sym: "Equiv_trans : Π {A : U}. Π {a b c : A}. Equiv a b → Equiv b c → Equiv a c",
                        red: &[
                            "∀ {A : U}. ∀ {a b : A}. ∀ e : Equiv a b. Equiv_trans (Equiv_refl a) e :≡ e",
                            "Equiv_trans {U} :≡ λ {A B C}. λ e f. Sigma_intro {A → C} (IsEquiv {A} {C}) (λ a. Equiv_U_to f (Equiv_U_to e a)) (IsEquiv_trans (Sigma_snd e) (Sigma_snd f))",
                            "Equiv_trans {Unit} :≡ λ {_ _ _}. λ _ _. unit",
                            "∀ {A : U}. ∀ P : A → U. Equiv_trans {Pi P} :≡ λ {f g h}. λ efg egh. λ a : A. trans (efg a) (egh a)",
                            "∀ {A : U}. ∀ P : A → U. Equiv_trans {Sigma P} :≡ λ {p q r}. λ epq eqr. Sigma_intro (λ e_fst : Sigma_fst p = Sigma_fst r. Sigma_snd p =[ap P e_fst] Sigma_snd r) (trans {A} {Sigma_fst p} {Sigma_fst q} {Sigma_fst r} (Sigma_fst epq) (Sigma_fst eqr)) (DepEq_trans {P (Sigma_fst p)} {P (Sigma_fst q)} {P (Sigma_fst r)} {ap P (Sigma_fst epq)} {ap P (Sigma_fst eqr)} {Sigma_snd p} {Sigma_snd q} {Sigma_snd r} (Sigma_snd epq) (Sigma_snd eqr))",
                            "∀ {A : U}. ∀ a b : A. Equiv_trans {a = b} :≡ λ {e f g}. trans {Equiv a b} {Eq_to_Equiv e} {Eq_to_Equiv f} {Eq_to_Equiv g}",
                            "∀ {A B : U}. ∀ f : A → B. Equiv_trans {IsEquiv f} :≡ λ {_ _ _}. λ _ _. unit",
                        ],
                    },
                    DefInit {
                        sym: "Equiv_mid : Π {A : U}. Π {a b : A}. Equiv a b → A",
                        red: &[
                            // We can propagate the mid point from the contents of each equivalence,
                            // except that type equivalences don't actually have any obvious mid
                            // point, so we just place them completely on the left side.
                            "Equiv_mid {U} :≡ λ {A B}. λ _. B",
                            "Equiv_mid {Unit} :≡ λ {a b}. λ _. b",
                            "∀ {A : U}. ∀ P : A → U. Equiv_mid {Pi P} :≡ λ {f g}. λ e. λ a : A. mid (e a)",
                            "∀ {A : U}. ∀ P : A → U. Equiv_mid {Sigma P} :≡ λ {p q}. λ e. Sigma_intro P (mid (Sigma_fst e)) (to (mid_ap P (Sigma_fst e)) (DepEq_mid {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} {Sigma_snd p} {Sigma_snd q} (Sigma_snd e)))",
                            "∀ {A : U}. ∀ a b : A. Equiv_mid {a = b} :≡ λ {e f}. λ eef. Equiv_to_Eq (mid eef)",
                            "∀ {A B : U}. ∀ f : A → B. Equiv_mid {IsEquiv f} :≡ λ {h i}. λ _. i",
                        ],
                    },
                    DefInit {
                        sym: "Equiv_left : Π {A : U}. Π {a b : A}. Π e : Equiv a b. Equiv a (Equiv_mid e)",
                        red: &[
                            "Equiv_left {U} :≡ λ {A B}. λ e. e",
                            "Equiv_left {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. Equiv_left {Pi P} :≡ λ {f g}. λ e. λ a : A. left (e a)",
                            "∀ {A : U}. ∀ P : A → U. Equiv_left {Sigma P} :≡ λ {p q}. λ e. Sigma_intro (λ e_fst : Sigma_fst p = mid (Sigma_fst e). Sigma_snd p =[ap P e_fst] to (mid_ap P (Sigma_fst e)) (DepEq_mid {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} {Sigma_snd p} {Sigma_snd q} (Sigma_snd e))) (left (Sigma_fst e)) (sorry _)", // (DepEq_left {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} {Sigma_snd p} {Sigma_snd q} (Sigma_snd e))
                            "∀ {A : U}. ∀ a b : A. Equiv_left {a = b} :≡ λ {e f}. λ eef. left eef",
                            "∀ {A B : U}. ∀ f : A → B. Equiv_left {IsEquiv f} :≡ λ {_ _}. λ _. unit",
                        ],
                    },
                    DefInit {
                        sym: "Equiv_right : Π {A : U}. Π {a b : A}. Π e : Equiv a b. Equiv b (Equiv_mid e)",
                        red: &[
                            "Equiv_right {U} :≡ λ {A B}. λ e. Equiv_refl B",
                            "Equiv_right {Unit} :≡ λ {_ _}. λ _. unit",
                            "∀ {A : U}. ∀ P : A → U. Equiv_right {Pi P} :≡ λ {f g}. λ e. λ a : A. right (e a)",
                            "∀ {A : U}. ∀ P : A → U. Equiv_right {Sigma P} :≡ λ {p q}. λ e. Sigma_intro (λ e_fst : Sigma_fst q = mid (Sigma_fst e). Sigma_snd q =[ap P e_fst] to (mid_ap P (Sigma_fst e)) (DepEq_mid {P (Sigma_fst p)} {P (Sigma_fst q)} {ap P (Sigma_fst e)} {Sigma_snd p} {Sigma_snd q} (Sigma_snd e))) (right (Sigma_fst e)) (sorry _)",
                            "∀ {A : U}. ∀ a b : A. Equiv_right {a = b} :≡ λ {e f}. λ eef. right eef",
                            "∀ {A B : U}. ∀ f : A → B. Equiv_right {IsEquiv f} :≡ λ {_ _}. λ _. unit",
                        ],
                    },
                    DefInit {
                        sym: "Equiv_trans_left_right: Π {A : U}. Π {a b : A}. Π e : Equiv a b. Equiv_trans (Equiv_left e) (Equiv_symm (Equiv_right e)) = e",
                        red: &["Equiv_trans_left_right :≡ λ {A a b}. λ e. sorry _"],
                    },
                    DefInit {
                        sym: "Equiv_symm_symm: Π {A : U}. Π {a b : A}. Π e : Equiv a b. Equiv_symm (Equiv_symm e) = e",
                        red: &["Equiv_symm_symm :≡ λ {A a b}. λ e. sorry _"],
                    },
                    DefInit {
                        sym: "Equiv_trans_refl: Π {A : U}. Π {a b : A}. Π e : Equiv a b. Equiv_trans e (Equiv_refl b) = e",
                        red: &["Equiv_trans_refl :≡ λ {A a b}. λ e. sorry _"],
                    },
                    DefInit {
                        sym: "Equiv_trans_e_symm: Π {A : U}. Π {a b : A}. Π e : Equiv a b. Equiv_trans e (Equiv_symm e) = Equiv_refl a",
                        red: &["Equiv_trans_e_symm :≡ λ {A a b}. λ e. sorry _"],
                    },
                    DefInit {
                        sym: "Equiv_trans_symm_e: Π {A : U}. Π {a b : A}. Π e : Equiv a b. Equiv_trans (Equiv_symm e) e = Equiv_refl b",
                        red: &["Equiv_trans_symm_e :≡ λ {A a b}. λ e. sorry _"],
                    },
                    DefInit {
                        sym: "Equiv_symm_trans: Π {A : U}. Π {a b c : A}. Π e : Equiv a b. Π f : Equiv b c. Equiv_symm (Equiv_trans e f) = Equiv_trans (Equiv_symm f) (Equiv_symm e)",
                        red: &["Equiv_symm_trans :≡ λ {A a b c}. λ e f. sorry _"],
                    },
                    DefInit {
                        sym: "Equiv_assoc: Π {A : U}. Π {a b c d : A}. Π e : Equiv a b. Π f : Equiv b c. Π g : Equiv c d. Equiv_trans e (Equiv_trans f g) = Equiv_trans (Equiv_trans e f) g",
                        red: &["Equiv_assoc :≡ λ {A a b c d}. λ e f g. sorry _"],
                    },
                    DefInit {
                        sym: "Equiv_U_intro : Π {A B : U}. Π f : A → B. Π g : B → A. IsInv f g → Equiv A B",
                        red: &["Equiv_U_intro :≡ λ {A B}. λ f g e. Sigma_intro {A → B} (IsEquiv {A} {B}) f (IsEquiv_intro f g e)"],
                    },
                    DefInit {
                        sym: "Equiv_U_to : Π {A B : U}. Equiv A B → A → B",
                        red: &["Equiv_U_to :≡ λ {A B}. Sigma_fst {A → B} {IsEquiv {A} {B}}"],
                    },
                    DefInit {
                        sym: "Equiv_U_inv : Π {A B : U}. Equiv A B → B → A",
                        red: &["Equiv_U_inv :≡ λ {A B}. λ e. IsEquiv_inv (Sigma_snd e)"],
                    },
                    DefInit {
                        sym: "Equiv_U_inv_to : Π {A B : U}. Π e : Equiv A B. Π a : A. Equiv_U_inv e (Equiv_U_to e a) = a",
                        red: &["Equiv_U_inv_to :≡ λ {A B}. λ e a. sorry _"],
                    },
                    DefInit {
                        sym: "Equiv_U_to_inv : Π {A B : U}. Π e : Equiv A B. Π b : B. Equiv_U_to e (Equiv_U_inv e b) = b",
                        red: &["Equiv_U_to_inv :≡ λ {A B}. λ e b. sorry _"],
                    },
                    DefInit {
                        sym: "Equiv_Fun_nat : Π {A B : U}. Π {f g : A → B}. Π efg : Equiv f g. Π {a a' : A}. Π ea : a = a'. trans (efg a) (ap g ea) = trans (ap f ea) (efg a')",
                        red: &["Equiv_Fun_nat :≡ λ {A B f g}. λ efg. λ {a a'}. λ ea. sorry _"], // apd efg ea
                    },
                    DefInit {
                        sym: "Equiv_id_nat : Π {A : U}. Π {f : A → A}. Π ef : (Π a : A. f a = a). Π {a a' : A}. Π ea : a = a'. trans (ef a) ea = trans (ap f ea) (ef a')",
                        red: &["Equiv_id_nat :≡ λ {A f}. Equiv_Fun_nat {A} {A} {f} {id A}"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    // We define `IsEquiv f` as a primitive type instead of just `Sigma (IsInv f)`
                    // for several reasons:
                    // * We want to avoid `Equiv A B` from blowing up when reducing. In fact, we
                    //   need to go one step further and define `refl`, `symm`, and `trans` as
                    //   constructors that only reduce when queried.
                    // * We can give `IsEquiv` a custom equality, and of course we will just use
                    //   `Unit` since `IsEquiv` is contractible (as shown in the HoTT book).
                    // * And finally, it makes us less dependent on the exact definition, for which
                    //   there are different possibilities.
                    sym: "IsEquiv : Π {A B : U}. (A → B) → U",
                    red: &[],
                },
                defs: &[
                    DefInit {
                        sym: "IsEquiv_intro : Π {A B : U}. Π f : A → B. Π g : B → A. IsInv f g → IsEquiv f",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsEquiv_refl : Π A : U. IsEquiv (id A)",
                        red: &[],
                    },
                    DefInit {
                        sym: "IsEquiv_symm : Π {A B : U}. Π {f : A → B}. Π h : IsEquiv f. IsEquiv (IsEquiv_inv h)",
                        red: &[
                            "∀ A : U. IsEquiv_symm (IsEquiv_refl A) :≡ IsEquiv_refl A",
                        ],
                    },
                    DefInit {
                        sym: "IsEquiv_trans : Π {A B C : U}. Π {f : A → B}. Π {g : B → C}. Π hf : IsEquiv f. Π hg : IsEquiv g. IsEquiv {A} {C} (λ a. g (f a))",
                        red: &[
                            "∀ {A B : U}. ∀ {f : A → B}. ∀ h : IsEquiv f. IsEquiv_trans (IsEquiv_refl A) h :≡ h",
                        ],
                    },
                    DefInit {
                        sym: "IsEquiv_inv : Π {A B : U}. Π {f : A → B}. IsEquiv f → (B → A)",
                        red: &[
                            "∀ {A B : U}. ∀ f : A → B. ∀ g : B → A. ∀ efg : IsInv f g. IsEquiv_inv (IsEquiv_intro f g efg) :≡ g",
                            "∀ A : U. IsEquiv_inv (IsEquiv_refl A) :≡ id A",
                            "∀ {A B : U}. ∀ {f : A → B}. ∀ h : IsEquiv f. IsEquiv_inv (IsEquiv_symm h) :≡ f",
                            "∀ {A B C : U}. ∀ {f : A → B}. ∀ {g : B → C}. ∀ hf : IsEquiv f. ∀ hg : IsEquiv g. IsEquiv_inv (IsEquiv_trans hf hg) :≡ λ c : C. (IsEquiv_inv hf) (IsEquiv_inv hg c)",
                        ],
                    },
                    DefInit {
                        sym: "IsEquiv_isInv : Π {A B : U}. Π {f : A → B}. Π h : IsEquiv f. IsInv f (IsEquiv_inv h)",
                        red: &[
                            "∀ {A B : U}. ∀ f : A → B. ∀ g : B → A. ∀ efg : IsInv f g. IsEquiv_isInv (IsEquiv_intro f g efg) :≡ efg",
                            "∀ A : U. IsEquiv_isInv (IsEquiv_refl A) :≡ IsInv_refl A",
                            "∀ {A B : U}. ∀ {f : A → B}. ∀ h : IsEquiv f. IsEquiv_isInv (IsEquiv_symm h) :≡ IsInv_symm (IsEquiv_isInv h)",
                            "∀ {A B C : U}. ∀ {f : A → B}. ∀ {g : B → C}. ∀ hf : IsEquiv f. ∀ hg : IsEquiv g. IsEquiv_isInv (IsEquiv_trans hf hg) :≡ IsInv_trans (IsEquiv_isInv hf) (IsEquiv_isInv hg)",
                        ],
                    },
                    DefInit {
                        sym: "IsEquiv_qInv : Π {A B : U}. Π {f : A → B}. Π h : IsEquiv f. IsQuasiInv f (IsEquiv_inv h)",
                        red: &["IsEquiv_qInv :≡ λ {A B f}. λ h. IsInv_qInv (IsEquiv_isInv h)"],
                    },
                    DefInit {
                        sym: "IsEquiv_leftInv : Π {A B : U}. Π {f : A → B}. Π h : IsEquiv f. IsLeftInv f (IsEquiv_inv h)",
                        red: &["IsEquiv_leftInv :≡ λ {A B f}. λ h. IsInv_leftInv (IsEquiv_isInv h)"],
                    },
                    DefInit {
                        sym: "IsEquiv_rightInv : Π {A B : U}. Π {f : A → B}. Π h : IsEquiv f. IsLeftInv (IsEquiv_inv h) f",
                        red: &["IsEquiv_rightInv :≡ λ {A B f}. λ h. IsInv_rightInv (IsEquiv_isInv h)"],
                    },
                    DefInit {
                        sym: "IsEquiv_adj : Π {A B : U}. Π {f : A → B}. Π h : IsEquiv f. IsHalfAdjoint (IsEquiv_qInv h)",
                        red: &["IsEquiv_adj :≡ λ {A B f}. λ h. IsInv_adj (IsEquiv_isInv h)"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "IsInv : Π {A B : U}. (A → B) → (B → A) → U",
                    red: &["IsInv :≡ λ {A B}. λ fAB fBA. Sigma (IsHalfAdjoint {A} {B} {fAB} {fBA})"],
                },
                defs: &[
                    DefInit {
                        sym: "IsInv_intro : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. Π e : IsQuasiInv fAB fBA. IsHalfAdjoint e → IsInv fAB fBA",
                        red: &["IsInv_intro :≡ λ {A B fAB fBA}. Sigma_intro (IsHalfAdjoint {A} {B} {fAB} {fBA})"],
                    },
                    DefInit {
                        sym: "IsInv_qInv : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. IsInv fAB fBA → IsQuasiInv fAB fBA",
                        red: &["IsInv_qInv :≡ λ {A B fAB fBA}. Sigma_fst {IsQuasiInv fAB fBA} {IsHalfAdjoint {A} {B} {fAB} {fBA}}"],
                    },
                    DefInit {
                        sym: "IsInv_leftInv : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. IsInv fAB fBA → IsLeftInv fAB fBA",
                        red: &["IsInv_leftInv :≡ λ {A B fAB fBA}. λ e. IsQuasiInv_leftInv (IsInv_qInv e)"],
                    },
                    DefInit {
                        sym: "IsInv_rightInv : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. IsInv fAB fBA → IsLeftInv fBA fAB",
                        red: &["IsInv_rightInv :≡ λ {A B fAB fBA}. λ e. IsQuasiInv_rightInv (IsInv_qInv e)"],
                    },
                    DefInit {
                        sym: "IsInv_adj : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. Π e : IsInv fAB fBA. IsHalfAdjoint (IsInv_qInv e)",
                        red: &["IsInv_adj :≡ λ {A B fAB fBA}. Sigma_snd {IsQuasiInv fAB fBA} {IsHalfAdjoint {A} {B} {fAB} {fBA}}"],
                    },
                    DefInit {
                        sym: "IsInv_refl : Π A : U. IsInv (id A) (id A)",
                        red: &["IsInv_refl :≡ λ A. IsInv_intro (IsQuasiInv_refl A) (IsHalfAdjoint_refl A)"],
                    },
                    DefInit {
                        sym: "IsInv_symm : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. IsInv fAB fBA → IsInv fBA fAB",
                        red: &["IsInv_symm :≡ λ {A B fAB fBA}. λ eAB. IsInv_intro (IsQuasiInv_symm (IsInv_qInv eAB)) (IsHalfAdjoint_symm (IsInv_adj eAB))"],
                    },
                    DefInit {
                        sym: "IsInv_trans : Π {A B C : U}. Π {fAB : A → B}. Π {fBA : B → A}. Π {fBC : B → C}. Π {fCB : C → B}. IsInv fAB fBA → IsInv fBC fCB → IsInv (λ a. fBC (fAB a)) (λ c. fBA (fCB c))",
                        red: &["IsInv_trans :≡ λ {A B C fAB fBA fBC fCB}. λ eAB eBC. IsInv_intro (IsQuasiInv_trans (IsInv_qInv eAB) (IsInv_qInv eBC)) (IsHalfAdjoint_trans (IsInv_adj eAB) (IsInv_adj eBC))"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "IsQuasiInv : Π {A B : U}. (A → B) → (B → A) → U",
                    red: &["IsQuasiInv :≡ λ {A B}. λ fAB fBA. IsLeftInv fAB fBA × IsLeftInv fBA fAB"],
                },
                defs: &[
                    DefInit {
                        sym: "IsQuasiInv_intro : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. IsLeftInv fAB fBA → IsLeftInv fBA fAB → IsQuasiInv fAB fBA",
                        red: &["IsQuasiInv_intro :≡ λ {A B fAB fBA}. Pair_intro (IsLeftInv fAB fBA) (IsLeftInv fBA fAB)"],
                    },
                    DefInit {
                        sym: "IsQuasiInv_leftInv : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. IsQuasiInv fAB fBA → IsLeftInv fAB fBA",
                        red: &["IsQuasiInv_leftInv :≡ λ {A B fAB fBA}. Pair_fst {IsLeftInv fAB fBA} {IsLeftInv fBA fAB}"],
                    },
                    DefInit {
                        sym: "IsQuasiInv_rightInv : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. IsQuasiInv fAB fBA → IsLeftInv fBA fAB",
                        red: &["IsQuasiInv_rightInv :≡ λ {A B fAB fBA}. Pair_snd {IsLeftInv fAB fBA} {IsLeftInv fBA fAB}"],
                    },
                    DefInit {
                        sym: "IsQuasiInv_refl : Π A : U. IsQuasiInv (id A) (id A)",
                        red: &["IsQuasiInv_refl :≡ λ A. IsQuasiInv_intro (IsLeftInv_refl A) (IsLeftInv_refl A)"],
                    },
                    DefInit {
                        sym: "IsQuasiInv_symm : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. IsQuasiInv fAB fBA → IsQuasiInv fBA fAB",
                        red: &["IsQuasiInv_symm :≡ λ {A B fAB fBA}. λ eAB. IsQuasiInv_intro (IsQuasiInv_rightInv eAB) (IsQuasiInv_leftInv eAB)"],
                    },
                    DefInit {
                        sym: "IsQuasiInv_trans : Π {A B C : U}. Π {fAB : A → B}. Π {fBA : B → A}. Π {fBC : B → C}. Π {fCB : C → B}. IsQuasiInv fAB fBA → IsQuasiInv fBC fCB → IsQuasiInv (λ a. fBC (fAB a)) (λ c. fBA (fCB c))",
                        red: &["IsQuasiInv_trans :≡ λ {A B C fAB fBA fBC fCB}. λ eAB eBC. IsQuasiInv_intro (IsLeftInv_trans (IsQuasiInv_leftInv eAB) (IsQuasiInv_leftInv eBC)) (IsLeftInv_trans (IsQuasiInv_rightInv eBC) (IsQuasiInv_rightInv eAB))"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "IsLeftInv : Π {A B : U}. (A → B) → (B → A) → U",
                    red: &["IsLeftInv :≡ λ {A B}. λ fAB fBA. Π a : A. fBA (fAB a) = a"],
                },
                defs: &[
                    DefInit {
                        sym: "IsLeftInv_refl : Π A : U. IsLeftInv (id A) (id A)",
                        red: &["IsLeftInv_refl :≡ λ A. λ a : A. refl a"],
                    },
                    DefInit {
                        sym: "IsLeftInv_trans : Π {A B C : U}. Π {fAB : A → B}. Π {fBA : B → A}. Π {fBC : B → C}. Π {fCB : C → B}. IsLeftInv fAB fBA → IsLeftInv fBC fCB → IsLeftInv (λ a. fBC (fAB a)) (λ c. fBA (fCB c))",
                        red: &["IsLeftInv_trans :≡ λ {A B C fAB fBA fBC fCB}. λ eABA eBCB. λ a : A. trans (ap fBA (eBCB (fAB a))) (eABA a)"],
                    },
                ],
            },
            TypeInit {
                ctor: DefInit {
                    sym: "IsHalfAdjoint : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. IsQuasiInv fAB fBA → U",
                    red: &["IsHalfAdjoint :≡ λ {A B fAB fBA}. λ eAB. Π a : A. ap fAB (IsQuasiInv_leftInv eAB a) = IsQuasiInv_rightInv eAB (fAB a)"],
                },
                defs: &[
                    DefInit {
                        sym: "IsHalfAdjoint_refl : Π A : U. IsHalfAdjoint (IsQuasiInv_refl A)",
                        red: &["IsHalfAdjoint_refl :≡ λ A. λ a : A. refl (refl a)"],
                    },
                    DefInit {
                        sym: "IsHalfAdjoint_symm : Π {A B : U}. Π {fAB : A → B}. Π {fBA : B → A}. Π {eAB : IsQuasiInv fAB fBA}. IsHalfAdjoint eAB → IsHalfAdjoint (IsQuasiInv_symm eAB)",
                        red: &["IsHalfAdjoint_symm :≡ λ {A B fAB fBA eAB}. λ efAB. λ b : B. sorry _"],
                    },
                    DefInit {
                        sym: "IsHalfAdjoint_trans : Π {A B C : U}. Π {fAB : A → B}. Π {fBA : B → A}. Π {fBC : B → C}. Π {fCB : C → B}. Π {eAB : IsQuasiInv fAB fBA}. Π {eBC : IsQuasiInv fBC fCB}. IsHalfAdjoint eAB → IsHalfAdjoint eBC → IsHalfAdjoint (IsQuasiInv_trans eAB eBC)",
                        red: &["IsHalfAdjoint_trans :≡ λ {A B C fAB fBA fBC fCB eAB eBC}. \
                                                       [eABA ⫽ IsQuasiInv_leftInv eAB] [eBAB ⫽ IsQuasiInv_rightInv eAB] \
                                                       [eBCB ⫽ IsQuasiInv_leftInv eBC] [eCBC ⫽ IsQuasiInv_rightInv eBC] \
                                                       λ efAB : (Π a : A. ap fAB (eABA a) = eBAB (fAB a)). \
                                                       λ efBC : (Π b : B. ap fBC (eBCB b) = eCBC (fBC b)). \
                                                       λ a : A. \
                                                       [h1 : trans (ap fAB (ap fBA (eBCB (fAB a)))) (ap fAB (eABA a)) = \
                                                             trans (ap fAB (ap fBA (eBCB (fAB a)))) (eBAB (fAB a)) \
                                                           ⫽ ap_trans_2 (ap fAB (ap fBA (eBCB (fAB a)))) (efAB a)] \
                                                       [h2 : trans (ap fAB (ap fBA (eBCB (fAB a)))) (eBAB (fAB a)) = \
                                                             trans (eBAB (fCB (fBC (fAB a)))) (eBCB (fAB a)) \
                                                           ⫽ symm (Equiv_id_nat {B} {λ b. fAB (fBA b)} eBAB (eBCB (fAB a)))] \
                                                       [h3 : ap fBC (trans (eBAB (fCB (fBC (fAB a)))) (eBCB (fAB a))) = \
                                                             trans (ap fBC (eBAB (fCB (fBC (fAB a))))) (eCBC (fBC (fAB a))) \
                                                           ⫽ ap_trans_2 (ap fBC (eBAB (fCB (fBC (fAB a))))) (efBC (fAB a))] \
                                                       trans (ap_ap fBC (trans h1 h2)) h3"],
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
                    // For a similar reason, we want to reduce application to `refl`, `symm`, and
                    // `trans` generically. As a consequence, we need to restrict other reductions
                    // to `Equiv_to_Eq`, except where we expect the result to be definitionally
                    // equal. (At some point, we should check whether the restrictions are really
                    // necessary in all cases.)
                    "∀ {A B : U}. ∀ f : A → B. ∀ {a b : A}. ∀ e : Equiv a b. ap f (Equiv_to_Eq e) :≡ ap' f (Equiv_to_Eq e)",
                    "∀ {A B : U}. ∀ f : A → B. ∀ a : A. ap f (refl a) :≡ refl (f a)",
                    "∀ {A B : U}. ∀ f : A → B. ∀ {a b : A}. ∀ e : a = b. ap f (symm e) :≡ symm (ap f e)",
                    "∀ {A B : U}. ∀ f : A → B. ∀ {a b c : A}. ∀ eab : a = b. ∀ ebc : b = c. ap f (trans eab ebc) :≡ trans (ap f eab) (ap f ebc)",
                    "∀ A : U. ap (id A) :≡ λ {a a'}. λ e. e",
                    "∀ A : U. ∀ {B : U}. ∀ b : B. ap (const A b) :≡ λ {a a'}. λ e. refl b",
                    "∀ {A B C : U}. ∀ g : B → C. ∀ f : A → B. ap {A} {C} (subst {A} {const A B} {const A (const B C)} (const A g) f) :≡ λ {a a'}. λ e. ap g (ap f e)",
                ],
            },
            DefInit {
                sym: "ap' : Π {A B : U}. Π f : A → B. Π {a a' : A}. a = a' → f a = f a'",
                red: &[
                    // Type constructors
                    "∀ {A : U}. ∀ a : A. ∀ {b b' : A}. ∀ e : b = b'. ap' (Eq a) e :≡ Equiv_to_Eq (Equiv_U_intro (λ f : a = b. trans f e) (λ f : a = b'. trans f (symm e)) (sorry _))",
                    // TODO
                    // Combinators
                    "∀ A : U. ap' (id A) :≡ λ {a a'}. λ e. e",
                    "∀ A : U. ∀ {B : U}. ∀ b : B. ap' (const A b) :≡ λ {a a'}. λ e. refl b",
                    "∀ A B : U. ∀ {b b' : B}. ∀ e : b = b'. ap' (const A {B}) e :≡ Equiv_to_Eq (λ a : A. e)",
                    // Note: Due to the reduction rule of `trans`, it is important that the first
                    // argument of `subst` becomes `refl` when `g` is constant on `A`.
                    "∀ {A B C : U}. ∀ g : A → B → C. ∀ f : A → B. ap' {A} {C} (subst {A} {const A B} {const A (const B C)} g f) :≡ λ {a a'}. λ e. trans {C} {g a (f a)} {g a' (f a)} {g a' (f a')} (Eq_to_Equiv (ap g e) (f a)) (ap (g a') (ap f e))",
                    //"∀ {A : U}. ∀ {P : A → U}. ∀ {C : U}. ∀ g : (Π a : A. P a → C). ∀ f : Pi P. ap' {A} {C} (subst {A} {P} {λ a b. C} g f) :≡ λ {a a'}. λ e. trans {C} {g a (f a)} {g a' (f a)} {g a' (f a')} (Eq_to_Equiv (apd g e) (f a)) (ap (g a') (apd f e))",
                    // TODO other elimination functions
                ],
            },
            DefInit {
                sym: "ap_eq : Π {A B : U}. Π f : A → B. Π {a a' : A}. Π e : a = a'. ap f e = ap' f e",
                red: &["ap_eq :≡ sorry _"],
            },
            DefInit {
                sym: "apd : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a a' : A}. Π e : a = a'. f a =[ap P e] f a'",
                red: &[
                    // See above.
                    "∀ A B : U. apd {A} {const A B} :≡ ap {A} {B}",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ {a b : A}. ∀ e : Equiv a b. apd f (Equiv_to_Eq e) :≡ apd' f (Equiv_to_Eq e)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ a : A. apd f (refl a) :≡ DepEq_refl (f a)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ {a b : A}. ∀ e : a = b. apd f (symm e) :≡ DepEq_symm (apd f e)",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ f : Pi P. ∀ {a b c : A}. ∀ eab : a = b. ∀ ebc : b = c. apd f (trans eab ebc) :≡ DepEq_trans (apd f eab) (apd f ebc)",
                ],
            },
            DefInit {
                sym: "apd' : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a a' : A}. Π e : a = a'. f a =[ap P e] f a'",
                red: &[
                    "∀ A B : U. apd' {A} {const A B} :≡ ap' {A} {B}",
                    "∀ {A : U}. ∀ {P : A → U}. ∀ {Q : (Π a : A. P a → U)}. ∀ g : (Π a : A. Pi (Q a)). ∀ f : Pi P. apd' (subst g f) :≡ λ {a a'}. λ e. sorry _",
                    // TODO
                ],
            },
            DefInit {
                sym: "apd'' : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a a' : A}. Π e : a = a'. f a =[ap' P e] f a'",
                red: &["apd'' :≡ λ {A P}. λ f. λ {a a'}. λ e. sorry _"],
            },
            DefInit {
                sym: "apd_eq : Π {A : U}. Π {P : A → U}. Π f : Pi P. Π {a a' : A}. Π e : a = a'. apd f e = apd' f e",
                red: &["apd_eq :≡ sorry _"],
            },
            DefInit {
                sym: "mid_ap : Π {A : U}. Π P : A → U. Π {a a' : A}. Π e : a = a'. mid (ap P e) = P (mid e)",
                red: &["mid_ap :≡ sorry _"], // Trivial, but we should try to output good terms (often refl).
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
                sym: "ap_ap : Π {A B : U}. Π f : A → B. Π {a a' : A}. Π {e e' : a = a'}. e = e' → ap f e = ap f e'",
                red: &["ap_ap :≡ λ {A B}. λ f. λ {a a'}. ap (ap f {a} {a'})"],
            },
            DefInit {
                sym: "ap_symm : Π {A : U}. Π {a b : A}. Π {e e' : a = b}. e = e' → symm e = symm e'",
                red: &["ap_symm :≡ λ {A a b e e'}. λ he. ap (symm {A} {a} {b}) he"],
            },
            DefInit {
                sym: "ap_trans_1 : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π f : b = c. trans e f = trans e' f",
                red: &["ap_trans_1 :≡ λ {A a b c e e'}. λ he f. Eq_to_Equiv (ap (trans {A} {a} {b} {c}) he) f"],
            },
            DefInit {
                sym: "ap_trans_2 : Π {A : U}. Π {a b c : A}. Π e : a = b. Π {f f' : b = c}. f = f' → trans e f = trans e f'",
                red: &["ap_trans_2 :≡ λ {A a b c}. λ e. λ {f f'}. λ hf. ap (trans {A} {a} {b} {c} e) hf"],
            },
            DefInit {
                sym: "ap_trans : Π {A : U}. Π {a b c : A}. Π {e e' : a = b}. e = e' → Π {f f' : b = c}. f = f' → trans e f = trans e' f'",
                red: &["ap_trans :≡ λ {A a b c e e'}. λ he. λ {f f'}. λ hf. trans (ap_trans_1 he f) (ap_trans_2 e' hf)"],
            },
            DefInit {
                sym: "apj : Π {A : U}. Π {a a' : A}. Π P : (Π b : A. a = b → U). Π e : a = a'. P a (refl a) = P a' e",
                red: &["apj :≡ λ {A a a'}. λ P e. sorry _"], // trans _ (trans (Eq_to_Equiv {_} {_} {_} (apd P e) e) _)
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
    use crate::generic::context_object::*;

    use super::*;

    use anyhow::Result;

    #[test]
    fn test_mltt() -> Result<()> {
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
            "Π {A : U}. Π {P : A → U}. Π {Q : (Π a : A. P a → U)}. (Π a : A. Pi {P a} (Q a)) → (Π f : Pi {A} P. Π a : A. Q a (f a))"
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
        assert_eq!(const_ctor_occ.print(&root_ctx), "λ A : U. λ A : U. A⁺");
        assert_eq!(const_ctor_occ, const_ctor);

        let const_id_ctor_occ = Expr::parse("λ A A : U. A", &root_ctx)?;
        assert_eq!(const_id_ctor_occ.print(&root_ctx), "λ A : U. λ A : U. A");
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
            "Pi {U} (subst {U} {λ {A : U}. (A → U) → U} {λ {A : U}. λ _ : (A → U) → U. U} (λ {A : U}. Pi {A → U}) (λ {A : U}. λ {P : A → U}. Π {Q : (Π a : A. P a → U)}. (Π a : A. Pi {P a} (Q a)) → (Π f : Pi {A} P. Π a : A. Q a (f a))))"
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

    // TODO: check that left sides of reduction rules are irreducible (without that reduction rule)
    // TODO: check for superfluous variables in reduction rules
    // TODO: test that all declared types reduce uniquely (are confluent)
    // TODO: test that specific known terms with multiple reductions are confluent
}
