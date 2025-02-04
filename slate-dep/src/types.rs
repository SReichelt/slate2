//! We represent dependent types as Rust types by bundling all value dependencies of an instance,
//! i.e. instead of a type family we always work with the corresponding sigma type. Consequently, we
//! generally cannot isolate the second field of a dependent pair because we cannot express its
//! type, but we do have a projection to the first field (with its bundled dependencies), which we
//! can generally regard as "a function that returns the dependencies of the instance", although
//! what the dependencies of an instance are depends on the point of view.
//!
//! Whenever we require dependencies to adhere to some constraint, the constraint is not visible in
//! the Rust types but checked at runtime, preferably within the constructor of an instance that can
//! then be regarded as having an appropriately constrained type.
//!
//! The bundling approach has consequences for our handling of equality. If we had dependencies, we
//! would say that the equality of an instance lies over the equalities of its dependencies. Since
//! we bundle everything, we only have equalities of those bundled instances, but the projection
//! functions are required to respect equality, so we can regard the corresponding equality function
//! as a projection function of equalities. Therefore, we can say that the dependencies of an
//! equality are given by the equality of the original dependencies.
//!
//! An equality, or more generally any relation, _also_ has a projection function that returns the
//! pair of instances being compared. Therefore, we can alternatively regard equality as a dependent
//! type over a pair. Both components of the pair carry a copy of their respective dependencies, so
//! if we want to view the components as instances of dependent types, we are generally dealing with
//! heterogenous pairs.

pub mod traits {
    use std::fmt::Debug;

    use super::{cat::*, impls::*};

    /// A trait that is implemented by all Rust types that we want to treat as types in our logic.
    pub trait Type: Clone {
        /// Verifies that `a` and `b` are equal in Rust terms (not just in terms of [`Type::Eq`]),
        /// and panics if they are not. This should be used whenever the equality would be
        /// guaranteed by dependent types, which implies that every violation is a bug.
        ///
        /// If the constructor of an object asserts that two specific instances are the same, then
        /// in mathematical terms the object contains that data only once.
        fn assert_same(a: &Self, b: &Self);

        /// A particular (higher) groupoid on the type that is respected by every [`Function`].
        ///
        /// Due to the way relations work, this type is not suitable for deciding whether two
        /// instances are equal or not. In fact, for two instances that are not equal, the type `Eq`
        /// is (hopefully) just not constructible in a way that references those two instances.
        type Eq: Groupoid<Self>;
    }

    pub fn refl<A: Type>(a: A) -> A::Eq {
        id::<A, A::Eq>(a)
    }

    /// A function between two types, which maps individual instances and also equalities.
    pub trait Function<A: Type, B: Type> {
        fn call(a: A) -> B;

        /// A function that maps equalities such that for `e: a0 = a1`,
        /// `Self::EqFn::call(e): Self::call(a0) = Self::call(a1)`. By `e: a0 = a1` we mean an
        /// `e: A::Eq` such that `dep(e)` yields `(a0, a1)` strictly, i.e. according to
        /// [`Type::assert_same`].
        ///
        /// In particular, this ensures that for every `Fam: Family<A>` and `e: Fam::Eq`, passing
        /// `e` to `Fam::DepFn::EqFn` yields the equality on `A` that "underlies" `e`, such that
        /// its two endpoints match the dependencies of the endpoints of `e`.
        type EqFn: Function<A::Eq, B::Eq>;

        // TODO: respect groupoid
    }

    pub fn call_eq_fn<A: Type, B: Type, F: Function<A, B>>(ea: A::Eq) -> B::Eq {
        let (a0, a1) = dep(&ea);
        let b0 = F::call(a0);
        let b1 = F::call(a1);
        let eb = F::EqFn::call(ea);
        let (left, right) = dep(&eb);
        B::assert_same(&left, &b0);
        B::assert_same(&right, &b1);
        eb
    }

    /// An equality of two functions is given by a function that returns an equality where both
    /// sides match the result of the corresponding function.
    pub trait FunctionEq<A: Type, B: Type, F: Function<A, B>, G: Function<A, B>>:
        Function<A, B::Eq>
    {
    }

    pub fn call_fn_eq<
        A: Type,
        B: Type,
        F: Function<A, B>,
        G: Function<A, B>,
        FG: FunctionEq<A, B, F, G>,
    >(
        a: A,
    ) -> B::Eq {
        let fa = F::call(a.clone());
        let ga = G::call(a.clone());
        let eq = FG::call(a);
        let (left, right) = dep(&eq);
        B::assert_same(&left, &fa);
        B::assert_same(&right, &ga);
        eq
    }

    /// A type family, which is represented as a type that is considered to be the resulting sigma
    /// type, and a "projection" function that returns the first field of that sigma type, i.e. the
    /// "dependency" of the second field.
    pub trait Family<A: Type>: Type {
        type DepFn: Function<Self, A>;
    }

    pub fn dep<A: Type, Fam: Family<A>>(family: &Fam) -> A {
        Fam::DepFn::call(family.clone())
    }

    pub fn dep_eq<A: Type, Fam: Family<A>>(family_eq: &Fam::Eq) -> A::Eq {
        call_eq_fn::<Fam, A, Fam::DepFn>(family_eq.clone())
    }

    /// A "family function" is a function that maps dependencies, i.e. the results of
    /// [`Family::DepFn`] including equalities, strictly.
    pub trait FamilyFunction<A: Type, FamA: Family<A>, FamB: Family<A>>:
        Function<FamA, FamB>
    {
    }

    /// A relation is just a type family on a pair.
    pub trait Relation<A: Type>: Family<(A, A)> {}

    pub fn rel_dep<A: Type, Rel: Relation<A>>(rel: &Rel, rev: bool) -> (A, A) {
        let (left, right) = dep(rel);
        if rev {
            (right, left)
        } else {
            (left, right)
        }
    }

    pub fn rel_dep_eq<A: Type, Rel: Relation<A>>(rel_eq: &Rel::Eq, rev: bool) -> (A::Eq, A::Eq) {
        let (left_eq, right_eq) = dep_eq::<(A, A), Rel>(rel_eq).0;
        if rev {
            (right_eq, left_eq)
        } else {
            (left_eq, right_eq)
        }
    }

    /// A relation function is just a family function.
    pub trait RelationFunction<A: Type, RelA: Relation<A>, RelB: Relation<A>>:
        FamilyFunction<(A, A), RelA, RelB>
    {
    }

    /// A category is defined as a relation that specifies the morphisms between each pair of
    /// objects.
    pub trait Category<A: Type>: Relation<A> {
        /// A type that is additionally attached to each morphism in a [`super::cat::HomChain`], and
        /// which is `bool` if the category is defined to be a groupoid (so inverses can be obtained
        /// without explicitly constructing them), and `()` otherwise (corresponding to the flag
        /// always being `false`).
        type Inv: InvFlag;

        /// A function that reduces (i.e. composes) a "chain" of morphisms to a single morphism.
        /// This combines all category and (optionally) groupoid axioms in a way that results in
        /// more homogenous code (which should produce better terms).
        type ReduceFn: RelationFunction<A, HomChain<A, Self>, Self>;

        /// An function equality that specifies what a single-item hom chain is reduced to.
        type ReduceSingleEq: FunctionEq<
            Self,
            Self,
            CompFn<Self, HomChain<A, Self>, Self, HomChainSingleFn, Self::ReduceFn>,
            IdFn,
        >;
    }

    pub fn reduce<A: Type, Hom: Category<A>>(chain: HomChain<A, Hom>) -> Hom {
        Hom::ReduceFn::call(chain)
    }

    /// Returns an equality between the two reduced sides of the chain.
    pub fn reduce_eq<A: Type, Hom: Category<A>>(chain_eq: HomChainEq<A, Hom>) -> Hom::Eq {
        call_eq_fn::<HomChain<A, Hom>, Hom, Hom::ReduceFn>(chain_eq)
    }

    /// Given an equality of two chains where the right chain consists of a single uninverted hom,
    /// returns an equality between the reduced left side of the chain and the hom on the right.
    pub fn reduce_single_eq<A: Type, Hom: Category<A>>(
        chain_eq: HomChainEq<A, Hom>,
        hom: Hom,
    ) -> Hom::Eq {
        comp(
            reduce_eq(chain_eq),
            call_fn_eq::<
                Hom,
                Hom,
                CompFn<Hom, HomChain<A, Hom>, Hom, HomChainSingleFn, Hom::ReduceFn>,
                IdFn,
                Hom::ReduceSingleEq,
            >(hom),
        )
    }

    pub trait InvFlag: Copy + Default + Eq + Debug {
        /// If `true`, the morphism this flag is attached to must be inverted before processing it.
        fn get(self) -> bool;

        /// Negates the flag if possible, panics otherwise.
        fn negated(self) -> Self;
    }

    impl InvFlag for () {
        fn get(self) -> bool {
            false
        }

        fn negated(self) -> Self {
            panic!("inv flag of a category cannot be negated")
        }
    }

    impl InvFlag for bool {
        fn get(self) -> bool {
            self
        }

        fn negated(self) -> Self {
            !self
        }
    }

    /// A category that is known to be a groupoid.
    pub trait Groupoid<A: Type>: Category<A, Inv = bool> {}
}

pub mod impls {
    use std::{fmt::Debug, marker::PhantomData};

    use super::{cat::*, traits::*};

    pub trait Set: Clone + Eq + Debug {}

    impl<A: Set> Type for A {
        fn assert_same(a: &Self, b: &Self) {
            assert_eq!(a, b);
        }

        type Eq = SetEq<A>;
    }

    #[derive(Clone, PartialEq, Eq, Debug)]
    pub struct SetEq<A: Set>(pub A);

    impl<A: Set> Set for SetEq<A> {}

    impl<A: Set> Family<(A, A)> for SetEq<A> {
        type DepFn = SetEqDepFn;
    }

    pub struct SetEqDepFn;

    impl<A: Set> Function<SetEq<A>, (A, A)> for SetEqDepFn {
        fn call(e: SetEq<A>) -> (A, A) {
            (e.0.clone(), e.0)
        }

        type EqFn = CompFn<
            SetEq<SetEq<A>>,
            (SetEq<A>, SetEq<A>),
            <(A, A) as Type>::Eq,
            SetEqDepFn,
            MappedFamilyCtorFn,
        >;
    }

    impl<A: Set> Relation<A> for SetEq<A> {}

    impl<A: Set> Category<A> for SetEq<A> {
        type Inv = bool;

        type ReduceFn = SetEqReduceFn;

        type ReduceSingleEq = ReflFn<SetEq<A>, SetEq<A>, IdFn>;
    }

    pub struct SetEqReduceFn;

    impl<A: Set> Function<HomChain<A, SetEq<A>>, SetEq<A>> for SetEqReduceFn {
        fn call(chain: HomChain<A, SetEq<A>>) -> SetEq<A> {
            let (start, items) = chain.into_parts();
            for item in &items {
                assert_eq!(&item.hom.0, &start);
            }
            SetEq(start)
        }

        type EqFn = SetReduceEqFn;
    }

    impl<A: Set> FamilyFunction<(A, A), HomChain<A, SetEq<A>>, SetEq<A>> for SetEqReduceFn {}

    impl<A: Set> RelationFunction<A, HomChain<A, SetEq<A>>, SetEq<A>> for SetEqReduceFn {}

    impl<A: Set>
        FunctionEq<
            SetEq<A>,
            SetEq<A>,
            CompFn<SetEq<A>, HomChain<A, SetEq<A>>, SetEq<A>, HomChainSingleFn, SetEqReduceFn>,
            IdFn,
        > for ReflFn<SetEq<A>, SetEq<A>, IdFn>
    {
    }

    pub struct SetReduceEqFn;

    impl<A: Set> Function<HomChainEq<A, SetEq<A>>, SetEq<SetEq<A>>> for SetReduceEqFn {
        fn call(chain: HomChainEq<A, SetEq<A>>) -> SetEq<SetEq<A>> {
            SetEq(SetEq(chain.into_parts().0.into_parts().0))
        }

        type EqFn = TodoFn;
    }

    impl<A: Set> Groupoid<A> for SetEq<A> {}

    impl Set for () {}

    impl Set for usize {}
    impl Set for isize {}
    impl Set for i32 {}

    #[macro_export]
    macro_rules! impl_wrapper_type {
        (($($Generics:tt)*) ($Name:ident $($GenericArgs:tt)*); $Inner:ty; $CtorFn:ident, $GetFn:ident) => {
            impl $($Generics)* Type for $Name $($GenericArgs)* {
                fn assert_same(a: &Self, b: &Self) {
                    <$Inner as Type>::assert_same(&a.0, &b.0);
                }

                type Eq = MappedRel<$Inner, <$Inner as Type>::Eq, Self, $CtorFn, $GetFn>;
            }

            pub struct $CtorFn;

            impl $($Generics)*
                Function<$Inner, $Name $($GenericArgs)*> for $CtorFn
            {
                fn call(a: $Inner) -> $Name $($GenericArgs)* {
                    $Name::new(a)
                }

                type EqFn = MappedFamilyCtorFn;
            }

            pub struct $GetFn;

            impl $($Generics)* Function<$Name $($GenericArgs)*, $Inner> for $GetFn
            {
                fn call(a: $Name $($GenericArgs)*) -> $Inner {
                    a.0
                }

                type EqFn = MappedFamilyGetFn;
            }
        };
    }

    #[macro_export]
    macro_rules! wrapper_type {
        (($($Generics:tt)*) ($Name:ident $($GenericArgs:tt)*); $Inner:ty $(, $Extra:ty)?; $CtorFn:ident, $GetFn:ident) => {
            pub struct $Name $($Generics)*(pub $Inner $(, $Extra)?);

            impl $($Generics)* $Name $($GenericArgs)* {
                pub fn new(a: $Inner) -> Self {
                    $Name(a $(, <$Extra as Default>::default())?)
                }
            }

            impl $($Generics)* Clone for $Name $($GenericArgs)* {
                fn clone(&self) -> Self {
                    $Name(self.0.clone() $(, <$Extra as Default>::default())?)
                }
            }

            impl_wrapper_type!(($($Generics)*) ($Name $($GenericArgs)*); $Inner; $CtorFn, $GetFn);
        };
    }

    wrapper_type!((<A: Type>) (TrivialFamily<A>); A; TrivialFamilyCtorFn, TrivialFamilyGetFn);

    impl<A: Type> Family<A> for TrivialFamily<A> {
        type DepFn = TrivialFamilyDepFn;
    }

    pub struct TrivialFamilyDepFn;

    impl<A: Type> Function<TrivialFamily<A>, A> for TrivialFamilyDepFn {
        fn call(family: TrivialFamily<A>) -> A {
            family.0
        }

        type EqFn = MappedFamilyGetFn;
    }

    pub type TrivialRel<A> = TrivialFamily<(A, A)>;

    impl<A: Type> Relation<A> for TrivialRel<A> {}

    impl<A: Type> Category<A> for TrivialRel<A> {
        type Inv = bool;

        type ReduceFn = TrivialRelReduceFn;

        type ReduceSingleEq = TodoFn;
    }

    pub struct TrivialRelReduceFn;

    impl<A: Type> Function<HomChain<A, TrivialRel<A>>, TrivialRel<A>> for TrivialRelReduceFn {
        fn call(chain: HomChain<A, TrivialRel<A>>) -> TrivialRel<A> {
            let (start, items) = chain.into_parts();
            let end = items
                .into_iter()
                .last()
                .map(|item| item.hom.0 .1)
                .unwrap_or_else(|| start.clone());
            TrivialFamily((start, end))
        }

        type EqFn = TodoFn;
    }

    impl<A: Type> FamilyFunction<(A, A), HomChain<A, TrivialRel<A>>, TrivialRel<A>>
        for TrivialRelReduceFn
    {
    }

    impl<A: Type> RelationFunction<A, HomChain<A, TrivialRel<A>>, TrivialRel<A>>
        for TrivialRelReduceFn
    {
    }

    impl<A: Type> Groupoid<A> for TrivialRel<A> {}

    // Given a family on a type `A` and a strict equivalence between `A` and `B`, constructs a
    // family on `B`.
    wrapper_type!((<A: Type, Fam: Family<A>, B: Type, In: Function<A, B>, Out: Function<B, A>>)
                  (MappedFamily<A, Fam, B, In, Out>);
                  Fam, PhantomData<(A, B, In, Out)>;
                  MappedFamilyCtorFn, MappedFamilyGetFn);

    impl<A: Type, Fam: Family<A>, B: Type, In: Function<A, B>, Out: Function<B, A>> Family<B>
        for MappedFamily<A, Fam, B, In, Out>
    {
        type DepFn = Comp3Fn<
            MappedFamily<A, Fam, B, In, Out>,
            Fam,
            A,
            B,
            MappedFamilyGetFn,
            <Fam as Family<A>>::DepFn,
            In,
        >;
    }

    pub type MappedRel<A, Rel, B, In, Out> =
        MappedFamily<(A, A), Rel, (B, B), (In, In), (Out, Out)>;

    impl<A: Type, Rel: Relation<A>, B: Type, In: Function<A, B>, Out: Function<B, A>> Relation<B>
        for MappedRel<A, Rel, B, In, Out>
    {
    }

    impl<A: Type, Hom: Category<A>, B: Type, In: Function<A, B>, Out: Function<B, A>> Category<B>
        for MappedRel<A, Hom, B, In, Out>
    {
        type Inv = Hom::Inv;

        type ReduceFn = MappedRelReduceFn;

        type ReduceSingleEq = TodoFn;
    }

    pub struct MappedRelReduceFn;

    impl<A: Type, Hom: Category<A>, B: Type, In: Function<A, B>, Out: Function<B, A>>
        Function<HomChain<B, MappedRel<A, Hom, B, In, Out>>, MappedRel<A, Hom, B, In, Out>>
        for MappedRelReduceFn
    {
        fn call(
            chain: HomChain<B, MappedRel<A, Hom, B, In, Out>>,
        ) -> MappedRel<A, Hom, B, In, Out> {
            let (start, items) = chain.into_parts();
            MappedRel::new(reduce(HomChain::new(
                Out::call(start),
                items
                    .into_iter()
                    .map(|item| HomChainItem {
                        hom: item.hom.0,
                        inv: item.inv,
                    })
                    .collect(),
            )))
        }

        type EqFn = TodoFn;
    }

    impl<A: Type, Hom: Category<A>, B: Type, In: Function<A, B>, Out: Function<B, A>>
        FamilyFunction<
            (B, B),
            HomChain<B, MappedRel<A, Hom, B, In, Out>>,
            MappedRel<A, Hom, B, In, Out>,
        > for MappedRelReduceFn
    {
    }

    impl<A: Type, Hom: Category<A>, B: Type, In: Function<A, B>, Out: Function<B, A>>
        RelationFunction<
            B,
            HomChain<B, MappedRel<A, Hom, B, In, Out>>,
            MappedRel<A, Hom, B, In, Out>,
        > for MappedRelReduceFn
    {
    }

    impl<A: Type, Iso: Groupoid<A>, B: Type, In: Function<A, B>, Out: Function<B, A>> Groupoid<B>
        for MappedRel<A, Iso, B, In, Out>
    {
    }

    impl<A0: Type, A1: Type> Type for (A0, A1) {
        fn assert_same(a: &Self, b: &Self) {
            A0::assert_same(&a.0, &b.0);
            A1::assert_same(&a.1, &b.1);
        }

        type Eq = CrossRel<A0, A1, A0::Eq, A1::Eq>;
    }

    impl<A0: Type, A1: Type, Fam0: Family<A0>, Fam1: Family<A1>> Family<(A0, A1)> for (Fam0, Fam1) {
        type DepFn = (Fam0::DepFn, Fam1::DepFn);
    }

    pub type CrossRel<A0, A1, Rel0, Rel1> =
        MappedFamily<((A0, A0), (A1, A1)), (Rel0, Rel1), ((A0, A1), (A0, A1)), CrossFn, CrossFn>;

    impl<A0: Type, A1: Type, Rel0: Relation<A0>, Rel1: Relation<A1>> Relation<(A0, A1)>
        for CrossRel<A0, A1, Rel0, Rel1>
    {
    }

    impl<
            A0: Type,
            A1: Type,
            Inv: InvFlag,
            Hom0: Category<A0, Inv = Inv>,
            Hom1: Category<A1, Inv = Inv>,
        > Category<(A0, A1)> for CrossRel<A0, A1, Hom0, Hom1>
    {
        type Inv = Inv;

        type ReduceFn = TodoFn;

        type ReduceSingleEq = TodoFn;
    }

    impl<A0: Type, A1: Type, Iso0: Groupoid<A0>, Iso1: Groupoid<A1>> Groupoid<(A0, A1)>
        for CrossRel<A0, A1, Iso0, Iso1>
    {
    }

    pub struct TodoFn;

    impl<A: Type, B: Type> Function<A, B> for TodoFn {
        fn call(_: A) -> B {
            unimplemented!()
        }

        type EqFn = TodoFn;
    }

    impl<A: Type, FamA: Family<A>, FamB: Family<A>> FamilyFunction<A, FamA, FamB> for TodoFn {}

    impl<A: Type, RelA: Relation<A>, RelB: Relation<A>> RelationFunction<A, RelA, RelB> for TodoFn {}

    impl<A: Type, B: Type, F: Function<A, B>, G: Function<A, B>> FunctionEq<A, B, F, G> for TodoFn {}

    pub struct IdFn;

    impl<A: Type> Function<A, A> for IdFn {
        fn call(a: A) -> A {
            a
        }

        type EqFn = IdFn;
    }

    impl<A: Type, FamA: Family<A>> FamilyFunction<A, FamA, FamA> for IdFn {}

    impl<A: Type, RelA: Relation<A>> RelationFunction<A, RelA, RelA> for IdFn {}

    pub struct CompFn<A, B, C, F, G>(PhantomData<(A, B, C, F, G)>);

    impl<A: Type, B: Type, C: Type, F: Function<A, B>, G: Function<B, C>> Function<A, C>
        for CompFn<A, B, C, F, G>
    {
        fn call(a: A) -> C {
            G::call(F::call(a))
        }

        type EqFn = CompFn<A::Eq, B::Eq, C::Eq, F::EqFn, G::EqFn>;
    }

    impl<
            A: Type,
            FamA: Family<A>,
            FamB: Family<A>,
            FamC: Family<A>,
            F: FamilyFunction<A, FamA, FamB>,
            G: FamilyFunction<A, FamB, FamC>,
        > FamilyFunction<A, FamA, FamC> for CompFn<FamA, FamB, FamC, F, G>
    {
    }

    impl<
            A: Type,
            RelA: Relation<A>,
            RelB: Relation<A>,
            RelC: Relation<A>,
            F: RelationFunction<A, RelA, RelB>,
            G: RelationFunction<A, RelB, RelC>,
        > RelationFunction<A, RelA, RelC> for CompFn<RelA, RelB, RelC, F, G>
    {
    }

    pub type Comp3Fn<A, B, C, D, F, G, H> = CompFn<A, B, D, F, CompFn<B, C, D, G, H>>;

    impl<A0: Type, A1: Type, B0: Type, B1: Type, F0: Function<A0, B0>, F1: Function<A1, B1>>
        Function<(A0, A1), (B0, B1)> for (F0, F1)
    {
        fn call(a: (A0, A1)) -> (B0, B1) {
            (F0::call(a.0), F1::call(a.1))
        }

        type EqFn = Comp3Fn<
            <(A0, A1) as Type>::Eq,
            (A0::Eq, A1::Eq),
            (B0::Eq, B1::Eq),
            <(B0, B1) as Type>::Eq,
            MappedFamilyGetFn,
            (F0::EqFn, F1::EqFn),
            MappedFamilyCtorFn,
        >;
    }

    pub struct CrossFn;

    impl<A00: Type, A01: Type, A10: Type, A11: Type>
        Function<((A00, A01), (A10, A11)), ((A00, A10), (A01, A11))> for CrossFn
    {
        fn call(a: ((A00, A01), (A10, A11))) -> ((A00, A10), (A01, A11)) {
            ((a.0 .0, a.1 .0), (a.0 .1, a.1 .1))
        }

        type EqFn = Comp3Fn<
            <((A00, A01), (A10, A11)) as Type>::Eq,
            ((A00::Eq, A01::Eq), (A10::Eq, A11::Eq)),
            ((A00::Eq, A10::Eq), (A01::Eq, A11::Eq)),
            <((A00, A10), (A01, A11)) as Type>::Eq,
            CompFn<
                <((A00, A01), (A10, A11)) as Type>::Eq,
                (<(A00, A01) as Type>::Eq, <(A10, A11) as Type>::Eq),
                ((A00::Eq, A01::Eq), (A10::Eq, A11::Eq)),
                MappedFamilyGetFn,
                (MappedFamilyGetFn, MappedFamilyGetFn),
            >,
            CrossFn,
            CompFn<
                ((A00::Eq, A10::Eq), (A01::Eq, A11::Eq)),
                (<(A00, A10) as Type>::Eq, <(A01, A11) as Type>::Eq),
                <((A00, A10), (A01, A11)) as Type>::Eq,
                (MappedFamilyCtorFn, MappedFamilyCtorFn),
                MappedFamilyCtorFn,
            >,
        >;
    }

    pub struct ReflFn<A: Type, B: Type, F: Function<A, B>>(PhantomData<(A, B, F)>);

    impl<A: Type, B: Type, F: Function<A, B>> Function<A, B::Eq> for ReflFn<A, B, F> {
        fn call(a: A) -> B::Eq {
            refl(F::call(a))
        }

        type EqFn = TodoFn;
    }

    impl<A: Type, B: Type, F: Function<A, B>> FunctionEq<A, B, F, F> for ReflFn<A, B, F> {}
}

pub mod cat {
    use std::iter;

    use super::{impls::*, traits::*};

    pub fn id<A: Type, Hom: Category<A>>(a: A) -> Hom {
        reduce(HomChain::id(a))
    }

    pub fn comp<A: Type, Hom: Category<A>>(hom0: Hom, hom1: Hom) -> Hom {
        reduce(HomChain::comp(hom0, hom1))
    }

    pub fn inv<A: Type, Iso: Groupoid<A>>(iso: Iso) -> Iso {
        reduce(HomChain::inv(iso))
    }

    /// `inv(inv(iso)) = iso`
    pub fn inv_inv_eq<A: Type, Iso: Groupoid<A>>(iso: Iso) -> Iso::Eq {
        reduce_single_eq(
            HomChainEq::new(
                HomChain::inv(inv(iso.clone())),
                vec![HomChainEqItem::Expand(HomChainEqReduceItem {
                    start_idx: 0,
                    expanded: vec![HomChainItem {
                        hom: iso.clone(),
                        inv: false,
                    }],
                    reduced_inv: true,
                })],
            ),
            iso,
        )
    }

    #[derive(Clone)]
    pub struct HomChain<A: Type, Hom: Category<A>> {
        start: A,
        end: A,
        items: Vec<HomChainItem<A, Hom>>,
    }

    impl<A: Type, Hom: Category<A>> HomChain<A, Hom> {
        pub fn new(start: A, items: Vec<HomChainItem<A, Hom>>) -> Self {
            let mut end = start.clone();
            for item in &items {
                let (left, right) = item.dep();
                A::assert_same(&end, &left);
                end = right;
            }
            HomChain { start, end, items }
        }

        pub fn id(a: A) -> Self {
            HomChain::new(a, Vec::new())
        }

        pub fn single(hom: Hom) -> Self {
            let (start, end) = dep(&hom);
            HomChain {
                start,
                end,
                items: vec![HomChainItem {
                    hom,
                    inv: Default::default(),
                }],
            }
        }

        pub fn comp(hom0: Hom, hom1: Hom) -> Self {
            HomChain::new(
                dep(&hom0).0,
                vec![
                    HomChainItem {
                        hom: hom0,
                        inv: Default::default(),
                    },
                    HomChainItem {
                        hom: hom1,
                        inv: Default::default(),
                    },
                ],
            )
        }

        pub fn inv(iso: Hom) -> Self
        where
            Hom: Groupoid<A>,
        {
            HomChain::new(
                dep(&iso).1,
                vec![HomChainItem {
                    hom: iso,
                    inv: true,
                }],
            )
        }

        pub fn start(&self) -> &A {
            &self.start
        }

        pub fn end(&self) -> &A {
            &self.end
        }

        pub fn mid(&self, idx: usize) -> A {
            if idx == 0 {
                self.start.clone()
            } else {
                self.items[idx - 1].dep().1
            }
        }

        pub fn items(&self) -> &[HomChainItem<A, Hom>] {
            &self.items
        }

        pub fn into_parts(self) -> (A, Vec<HomChainItem<A, Hom>>) {
            (self.start, self.items)
        }

        fn inverted(self) -> Self {
            HomChain {
                start: self.end,
                end: self.start,
                items: self
                    .items
                    .into_iter()
                    .rev()
                    .map(HomChainItem::inverted)
                    .collect(),
            }
        }
    }

    impl<A: Type, Hom: Category<A>> Type for HomChain<A, Hom> {
        fn assert_same(a: &Self, b: &Self) {
            A::assert_same(&a.start, &b.start);
            assert_eq!(a.items.len(), b.items.len());
            for (a_item, b_item) in a.items.iter().zip(b.items.iter()) {
                HomChainItem::assert_same(a_item, b_item);
            }
        }

        type Eq = HomChainEq<A, Hom>;
    }

    impl<A: Type, Hom: Category<A>> Family<(A, A)> for HomChain<A, Hom> {
        type DepFn = HomChainDepFn;
    }

    pub struct HomChainDepFn;

    impl<A: Type, Hom: Category<A>> Function<HomChain<A, Hom>, (A, A)> for HomChainDepFn {
        fn call(chain: HomChain<A, Hom>) -> (A, A) {
            (chain.start.clone(), chain.end.clone())
        }

        type EqFn = TodoFn;
    }

    impl<A: Type, Hom: Category<A>> Relation<A> for HomChain<A, Hom> {}

    pub struct HomChainSingleFn;

    impl<A: Type, Hom: Category<A>> Function<Hom, HomChain<A, Hom>> for HomChainSingleFn {
        fn call(hom: Hom) -> HomChain<A, Hom> {
            HomChain::single(hom)
        }

        type EqFn = HomChainSingleEqFn;
    }

    impl<A: Type, Hom: Category<A>> FamilyFunction<(A, A), Hom, HomChain<A, Hom>> for HomChainSingleFn {}

    impl<A: Type, Hom: Category<A>> RelationFunction<A, Hom, HomChain<A, Hom>> for HomChainSingleFn {}

    pub struct HomChainSingleEqFn;

    impl<A: Type, Hom: Category<A>> Function<Hom::Eq, HomChainEq<A, Hom>> for HomChainSingleEqFn {
        fn call(hom_eq: Hom::Eq) -> HomChainEq<A, Hom> {
            let (left, right) = dep(&hom_eq);
            let (start_eq, end_eq) = rel_dep_eq::<A, Hom>(&hom_eq, false);
            HomChainEq {
                left: HomChain::single(left),
                right: HomChain::single(right),
                items: vec![HomChainEqItem::Inner(HomChainEqInnerItem {
                    start_eq,
                    end_eq,
                    hom_eqs: vec![hom_eq],
                    rev: false,
                })],
            }
        }

        type EqFn = TodoFn;
    }

    #[derive(Clone)]
    pub struct HomChainItem<A: Type, Hom: Category<A>> {
        pub hom: Hom,
        pub inv: Hom::Inv,
    }

    impl<A: Type, Hom: Category<A>> HomChainItem<A, Hom> {
        fn assert_same(a: &Self, b: &Self) {
            Hom::assert_same(&a.hom, &b.hom);
            assert_eq!(a.inv, b.inv);
        }

        fn dep(&self) -> (A, A) {
            let (left, right) = dep(&self.hom);
            if self.inv.get() {
                (right, left)
            } else {
                (left, right)
            }
        }

        fn inverted(self) -> Self {
            HomChainItem {
                inv: self.inv.negated(),
                ..self
            }
        }
    }

    #[derive(Clone)]
    pub struct HomChainEq<A: Type, Hom: Category<A>> {
        left: HomChain<A, Hom>,
        right: HomChain<A, Hom>,
        items: Vec<HomChainEqItem<A, Hom>>,
    }

    impl<A: Type, Hom: Category<A>> HomChainEq<A, Hom> {
        pub fn new(left: HomChain<A, Hom>, items: Vec<HomChainEqItem<A, Hom>>) -> Self {
            let mut end = left.clone();
            for item in &items {
                item.apply(&mut end, true);
            }
            HomChainEq {
                left,
                right: end,
                items,
            }
        }

        pub fn left(&self) -> &HomChain<A, Hom> {
            &self.left
        }

        pub fn right(&self) -> &HomChain<A, Hom> {
            &self.right
        }

        pub fn items(&self) -> &[HomChainEqItem<A, Hom>] {
            &self.items
        }

        pub fn into_parts(self) -> (HomChain<A, Hom>, Vec<HomChainEqItem<A, Hom>>) {
            (self.left, self.items)
        }

        pub fn reversed(self) -> Self {
            HomChainEq {
                left: self.right,
                right: self.left,
                items: self
                    .items
                    .into_iter()
                    .rev()
                    .map(HomChainEqItem::reversed)
                    .collect(),
            }
        }
    }

    impl<A: Type, Hom: Category<A>> Type for HomChainEq<A, Hom> {
        fn assert_same(a: &Self, b: &Self) {
            HomChain::assert_same(&a.left, &b.left);
            // Note that `end` is redundant.
            assert_eq!(a.items.len(), b.items.len());
            for (a_item, b_item) in a.items.iter().zip(b.items.iter()) {
                HomChainEqItem::assert_same(a_item, b_item);
            }
        }

        // TODO: An equality should consist of a list of transformations:
        // * Commuting unrelated steps.
        // * Flipping single-hom reduce/expand steps.
        // * Merging/splitting consecutive reduce or expand steps that "nest".
        //   Likely criterion: An expanding step can "eat" everything to its right that completely
        //   lies within the expanded range.
        // * Eliminating/introducing steps that compose to the identity.
        type Eq = TrivialRel<Self>;
    }

    impl<A: Type, Hom: Category<A>> Family<(HomChain<A, Hom>, HomChain<A, Hom>)>
        for HomChainEq<A, Hom>
    {
        type DepFn = HomChainEqDepFn;
    }

    pub struct HomChainEqDepFn;

    impl<A: Type, Hom: Category<A>>
        Function<HomChainEq<A, Hom>, (HomChain<A, Hom>, HomChain<A, Hom>)> for HomChainEqDepFn
    {
        fn call(chain_eq: HomChainEq<A, Hom>) -> (HomChain<A, Hom>, HomChain<A, Hom>) {
            (chain_eq.left.clone(), chain_eq.right.clone())
        }

        type EqFn = TodoFn;
    }

    impl<A: Type, Hom: Category<A>> Relation<HomChain<A, Hom>> for HomChainEq<A, Hom> {}

    impl<A: Type, Hom: Category<A>> Category<HomChain<A, Hom>> for HomChainEq<A, Hom> {
        type Inv = bool;

        type ReduceFn = HomChainEqReduceFn;

        type ReduceSingleEq = ReflFn<Self, Self, IdFn>;
    }

    pub struct HomChainEqReduceFn;

    impl<A: Type, Hom: Category<A>>
        Function<HomChain<HomChain<A, Hom>, HomChainEq<A, Hom>>, HomChainEq<A, Hom>>
        for HomChainEqReduceFn
    {
        fn call(chain: HomChain<HomChain<A, Hom>, HomChainEq<A, Hom>>) -> HomChainEq<A, Hom> {
            let mut current = &chain.start;
            let mut items =
                Vec::with_capacity(chain.items.iter().map(|item| item.hom.items.len()).sum());
            let mut temp: HomChain<A, Hom>;
            for item in chain.items {
                let chain_eq = if item.inv.get() {
                    item.hom.reversed()
                } else {
                    item.hom
                };
                HomChain::assert_same(&chain_eq.left, &current);
                items.extend(chain_eq.items);
                temp = chain_eq.right;
                current = &temp;
            }
            HomChain::assert_same(&chain.end, &current);
            HomChainEq {
                left: chain.start,
                right: chain.end,
                items,
            }
        }

        type EqFn = AssocReduceEqFn;
    }

    impl<A: Type, Hom: Category<A>>
        FamilyFunction<
            (HomChain<A, Hom>, HomChain<A, Hom>),
            HomChain<HomChain<A, Hom>, HomChainEq<A, Hom>>,
            HomChainEq<A, Hom>,
        > for HomChainEqReduceFn
    {
    }

    impl<A: Type, Hom: Category<A>>
        RelationFunction<
            HomChain<A, Hom>,
            HomChain<HomChain<A, Hom>, HomChainEq<A, Hom>>,
            HomChainEq<A, Hom>,
        > for HomChainEqReduceFn
    {
    }

    impl<A: Type, Hom: Category<A>>
        FunctionEq<
            HomChainEq<A, Hom>,
            HomChainEq<A, Hom>,
            CompFn<
                HomChainEq<A, Hom>,
                HomChain<HomChain<A, Hom>, HomChainEq<A, Hom>>,
                HomChainEq<A, Hom>,
                HomChainSingleFn,
                HomChainEqReduceFn,
            >,
            IdFn,
        > for ReflFn<HomChainEq<A, Hom>, HomChainEq<A, Hom>, IdFn>
    {
    }

    impl<A: Type, Hom: Category<A>> Groupoid<HomChain<A, Hom>> for HomChainEq<A, Hom> {}

    #[derive(Clone)]
    pub enum HomChainEqItem<A: Type, Hom: Category<A>> {
        Reduce(HomChainEqReduceItem<A, Hom>),
        Expand(HomChainEqReduceItem<A, Hom>),
        Inner(HomChainEqInnerItem<A, Hom>),
    }

    impl<A: Type, Hom: Category<A>> HomChainEqItem<A, Hom> {
        fn assert_same(a: &Self, b: &Self) {
            match (a, b) {
                (HomChainEqItem::Reduce(a_item), HomChainEqItem::Reduce(b_item)) => {
                    HomChainEqReduceItem::assert_same(a_item, b_item)
                }
                (HomChainEqItem::Expand(a_item), HomChainEqItem::Expand(b_item)) => {
                    HomChainEqReduceItem::assert_same(a_item, b_item)
                }
                (HomChainEqItem::Inner(a_item), HomChainEqItem::Inner(b_item)) => {
                    HomChainEqInnerItem::assert_same(a_item, b_item)
                }
                _ => panic!("hom chain eq items do not match"),
            }
        }

        fn apply(&self, chain: &mut HomChain<A, Hom>, check: bool) {
            match self {
                HomChainEqItem::Reduce(item) => item.reduce(chain, check),
                HomChainEqItem::Expand(item) => item.expand(chain, check),
                HomChainEqItem::Inner(item) => item.apply(chain, check),
            }
        }

        fn reversed(self) -> Self {
            match self {
                HomChainEqItem::Reduce(item) => HomChainEqItem::Expand(item),
                HomChainEqItem::Expand(item) => HomChainEqItem::Reduce(item),
                HomChainEqItem::Inner(item) => HomChainEqItem::Inner(item.reversed()),
            }
        }
    }

    #[derive(Clone)]
    pub struct HomChainEqReduceItem<A: Type, Hom: Category<A>> {
        /// The index within the hom chain where reducing/expanding is started.
        pub start_idx: usize,

        /// A copy of the part of the hom chain that should be reduced. In the "reduce" direction,
        /// only the length is relevant.
        pub expanded: Vec<HomChainItem<A, Hom>>,

        // Specifies that the reduction should result in an inverted morphism.
        pub reduced_inv: Hom::Inv,
    }

    impl<A: Type, Hom: Category<A>> HomChainEqReduceItem<A, Hom> {
        fn assert_same(a: &Self, b: &Self) {
            assert_eq!(a.start_idx, b.start_idx);
            assert_eq!(a.expanded.len(), b.expanded.len());
            for (a_item, b_item) in a.expanded.iter().zip(b.expanded.iter()) {
                HomChainItem::assert_same(a_item, b_item);
            }
        }

        fn reduce(&self, chain: &mut HomChain<A, Hom>, check: bool) {
            let end_idx = self.start_idx + self.expanded.len();
            assert!(end_idx <= chain.items.len());

            if check {
                for (expanded_item, chain_item) in self
                    .expanded
                    .iter()
                    .zip(chain.items.iter().skip(self.start_idx))
                {
                    HomChainItem::assert_same(expanded_item, chain_item);
                }
            }

            let mut expanded_chain = HomChain {
                start: chain.mid(self.start_idx),
                end: chain.mid(end_idx),
                items: self.expanded.clone(),
            };
            if self.reduced_inv.get() {
                expanded_chain = expanded_chain.inverted();
            }

            chain.items.splice(
                self.start_idx..end_idx,
                iter::once(HomChainItem {
                    hom: reduce(expanded_chain),
                    inv: self.reduced_inv,
                }),
            );
        }

        fn expand(&self, chain: &mut HomChain<A, Hom>, check: bool) {
            assert!(self.start_idx < chain.items.len());
            let chain_item = &chain.items[self.start_idx];
            assert!(chain_item.inv == self.reduced_inv);

            if check {
                let mut expanded_chain =
                    HomChain::new(chain.mid(self.start_idx), self.expanded.clone());
                if self.reduced_inv.get() {
                    expanded_chain = expanded_chain.inverted();
                }
                let reduced = reduce(expanded_chain);
                Hom::assert_same(&reduced, &chain_item.hom);
            }

            chain.items.splice(
                self.start_idx..=self.start_idx,
                self.expanded.iter().cloned(),
            );
        }
    }

    #[derive(Clone)]
    pub struct HomChainEqInnerItem<A: Type, Hom: Category<A>> {
        /// An equality between the start instances of the chains.
        start_eq: A::Eq,

        /// An equality between the end instances of the chains.
        end_eq: A::Eq,

        /// For each chain item, an equality between the left and right homs (regardless of whether
        /// the chain item is inverted).
        hom_eqs: Vec<Hom::Eq>,

        /// Specifies that the equalities within the item should be reversed when applying.
        rev: bool,
    }

    impl<A: Type, Hom: Category<A>> HomChainEqInnerItem<A, Hom> {
        pub fn new(start_eq: A::Eq, hom_eqs: Vec<Hom::Eq>, rev: bool) -> Self {
            let mut end_eq = start_eq.clone();
            for hom_eq in &hom_eqs {
                let (left_eq, right_eq) = rel_dep_eq::<A, Hom>(hom_eq, false);
                <(A, A) as Type>::assert_same(&dep(&end_eq), &dep(&left_eq));
                end_eq = right_eq;
            }
            HomChainEqInnerItem {
                start_eq,
                end_eq,
                hom_eqs,
                rev,
            }
        }

        fn assert_same(a: &Self, b: &Self) {
            A::Eq::assert_same(&a.start_eq, &b.start_eq);
            // Note that `end_eq` is redundant.
            assert_eq!(a.hom_eqs.len(), b.hom_eqs.len());
            for (a_eq, b_eq) in a.hom_eqs.iter().zip(b.hom_eqs.iter()) {
                Hom::Eq::assert_same(a_eq, b_eq);
            }
            assert_eq!(a.rev, b.rev);
        }

        fn apply(&self, chain: &mut HomChain<A, Hom>, check: bool) {
            let (start_left, start_right) = rel_dep(&self.start_eq, self.rev);
            if check {
                A::assert_same(&chain.start, &start_left);
            }
            chain.start = start_right;

            let (_, end_right) = rel_dep(&self.end_eq, self.rev);
            chain.end = end_right;

            assert_eq!(chain.items.len(), self.hom_eqs.len());
            for (chain_item, hom_eq) in chain.items.iter_mut().zip(self.hom_eqs.iter()) {
                let (left, right) = rel_dep(hom_eq, self.rev);
                if check {
                    Hom::assert_same(&chain_item.hom, &left);
                }
                chain_item.hom = right;
            }
        }

        fn reversed(self) -> Self {
            HomChainEqInnerItem {
                rev: !self.rev,
                ..self
            }
        }
    }

    /// A generic equality function for hom chain reductions that are strictly associative in the
    /// sense that a nested reduction always yields the same result as the reduction of the
    /// corresponding expanded chain.
    /// Requires equalities of morphisms to form a category on the equalities of objects. This is
    /// trivially the case if the category is actually the equality on objects.
    pub struct AssocReduceEqFn;

    impl<A: Type, Hom: Category<A, Eq: Category<A::Eq, Inv = Hom::Inv>>>
        Function<HomChainEq<A, Hom>, Hom::Eq> for AssocReduceEqFn
    {
        fn call(chain_eq: HomChainEq<A, Hom>) -> Hom::Eq {
            let (chain, chain_eq_items) = chain_eq.into_parts();
            let mut invs = chain.items.iter().map(|item| item.inv).collect::<Vec<_>>();
            let mut items = Vec::<HomChainItem<Hom, Hom::Eq>>::new();
            for item in chain_eq_items {
                match item {
                    HomChainEqItem::Reduce(item) => {
                        let end_idx = item.start_idx + item.expanded.len();
                        invs.splice(item.start_idx..end_idx, iter::once(item.reduced_inv));
                    }
                    HomChainEqItem::Expand(item) => {
                        invs.splice(
                            item.start_idx..=item.start_idx,
                            item.expanded.iter().map(|item| item.inv),
                        );
                    }
                    HomChainEqItem::Inner(item) => {
                        items.push(HomChainItem {
                            hom: reduce(HomChain::<A::Eq, Hom::Eq>::new(
                                item.start_eq,
                                item.hom_eqs
                                    .into_iter()
                                    .zip(invs.iter())
                                    .map(|(hom_eq, &inv)| HomChainItem { hom: hom_eq, inv })
                                    .collect(),
                            )),
                            inv: item.rev,
                        });
                    }
                }
            }
            reduce(HomChain::new(reduce(chain), items))
        }

        type EqFn = TodoFn;
    }
}

#[cfg(test)]
mod tests;
