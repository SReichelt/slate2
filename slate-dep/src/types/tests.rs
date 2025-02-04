use super::{cat::*, impls::*, traits::*};

use unordered_list::*;

mod unordered_list {
    use crate::impl_wrapper_type;

    use super::*;

    use std::collections::HashSet;

    #[derive(Clone)]
    pub struct UnorderedList<A: Type>(pub Vec<A>);

    impl<A: Type> Type for UnorderedList<A> {
        fn assert_same(a: &Self, b: &Self) {
            assert_eq!(a.0.len(), b.0.len());
            for (a_item, b_item) in a.0.iter().zip(b.0.iter()) {
                A::assert_same(a_item, b_item);
            }
        }

        type Eq = UnorderedListEq<A>;
    }

    #[derive(Clone)]
    pub struct UnorderedListEq<A: Type>(UnorderedList<UnorderedListEqItem<A>>);

    impl<A: Type> UnorderedListEq<A> {
        pub fn new(items: UnorderedList<UnorderedListEqItem<A>>) -> Self {
            let mut left_indices = HashSet::new();
            let mut right_indices = HashSet::new();
            for item in &items.0 {
                assert!(item.left_idx < items.0.len());
                assert!(item.right_idx < items.0.len());
                let left_inserted = left_indices.insert(item.left_idx);
                assert!(left_inserted);
                let right_inserted = right_indices.insert(item.right_idx);
                assert!(right_inserted);
            }

            UnorderedListEq(items)
        }
    }

    impl_wrapper_type!((<A: Type>) (UnorderedListEq<A>);
                       UnorderedList<UnorderedListEqItem<A>>;
                       UnorderedListEqCtorFn, UnorderedListEqGetFn);

    impl<A: Type> Family<(UnorderedList<A>, UnorderedList<A>)> for UnorderedListEq<A> {
        type DepFn = UnorderedListEqDepFn;
    }

    pub struct UnorderedListEqDepFn;

    impl<A: Type> Function<UnorderedListEq<A>, (UnorderedList<A>, UnorderedList<A>)>
        for UnorderedListEqDepFn
    {
        fn call(list_eq: UnorderedListEq<A>) -> (UnorderedList<A>, UnorderedList<A>) {
            let mut left_items = vec![None; list_eq.0 .0.len()];
            let mut right_items = vec![None; list_eq.0 .0.len()];
            for item in &list_eq.0 .0 {
                let (left, right) = dep(&item.eq);
                left_items[item.left_idx] = Some(left);
                right_items[item.right_idx] = Some(right);
            }
            let left_list = UnorderedList(left_items.into_iter().map(Option::unwrap).collect());
            let right_list = UnorderedList(right_items.into_iter().map(Option::unwrap).collect());
            (left_list, right_list)
        }

        type EqFn = TodoFn;
    }

    impl<A: Type> Relation<UnorderedList<A>> for UnorderedListEq<A> {}

    impl<A: Type> Category<UnorderedList<A>> for UnorderedListEq<A> {
        type Inv = bool;

        type ReduceFn = UnorderedListEqReduceFn;

        type ReduceSingleEq = UnorderedListEqReduceSingleEq;
    }

    pub struct UnorderedListEqReduceFn;

    impl<A: Type> Function<HomChain<UnorderedList<A>, UnorderedListEq<A>>, UnorderedListEq<A>>
        for UnorderedListEqReduceFn
    {
        fn call(chain: HomChain<UnorderedList<A>, UnorderedListEq<A>>) -> UnorderedListEq<A> {
            let (chain_start, chain_items) = chain.into_parts();

            let mut items = chain_start
                .0
                .into_iter()
                .enumerate()
                .map(|(idx, eq_start)| (idx, eq_start, Vec::<HomChainItem<A, A::Eq>>::new()))
                .collect::<Vec<_>>();

            for chain_item in chain_items {
                let mut item_indices = vec![usize::MAX; items.len()];
                for (idx, (right_idx, _, _)) in items.iter().enumerate() {
                    item_indices[*right_idx] = idx;
                }
                if chain_item.inv {
                    for eq_item in chain_item.hom.0 .0 {
                        let (right_idx, _, eq_items) = &mut items[item_indices[eq_item.right_idx]];
                        *right_idx = eq_item.left_idx;
                        eq_items.push(HomChainItem {
                            hom: eq_item.eq,
                            inv: true,
                        });
                    }
                } else {
                    for eq_item in chain_item.hom.0 .0 {
                        let (right_idx, _, eq_items) = &mut items[item_indices[eq_item.left_idx]];
                        *right_idx = eq_item.right_idx;
                        eq_items.push(HomChainItem {
                            hom: eq_item.eq,
                            inv: false,
                        });
                    }
                }
            }

            UnorderedListEq::new(UnorderedList(
                items
                    .into_iter()
                    .enumerate()
                    .map(
                        |(left_idx, (right_idx, eq_start, eq_items))| UnorderedListEqItem {
                            left_idx,
                            right_idx,
                            eq: reduce(HomChain::new(eq_start, eq_items)),
                        },
                    )
                    .collect(),
            ))
        }

        type EqFn = AssocReduceEqFn;
    }

    impl<A: Type>
        FamilyFunction<
            (UnorderedList<A>, UnorderedList<A>),
            HomChain<UnorderedList<A>, UnorderedListEq<A>>,
            UnorderedListEq<A>,
        > for UnorderedListEqReduceFn
    {
    }

    impl<A: Type>
        RelationFunction<
            UnorderedList<A>,
            HomChain<UnorderedList<A>, UnorderedListEq<A>>,
            UnorderedListEq<A>,
        > for UnorderedListEqReduceFn
    {
    }

    pub struct UnorderedListEqReduceSingleEq;

    impl<A: Type> Function<UnorderedListEq<A>, <UnorderedListEq<A> as Type>::Eq>
        for UnorderedListEqReduceSingleEq
    {
        fn call(list_eq: UnorderedListEq<A>) -> <UnorderedListEq<A> as Type>::Eq {
            // Since `UnorderedListEqReduceFn` sorts items according to the start list, which
            // corresponds to the left side of every item via `dep`, we need to connect the left
            // indices on the left (i.e. reduced) side with eq item indices on the right.
            let eq_items = list_eq
                .0
                 .0
                .into_iter()
                .enumerate()
                .map(|(idx, eq_item)| UnorderedListEqItem {
                    left_idx: eq_item.left_idx,
                    right_idx: idx,
                    eq: refl(eq_item),
                })
                .collect();
            MappedRel::new(UnorderedListEq::new(UnorderedList(eq_items)))
        }

        type EqFn = TodoFn;
    }

    impl<A: Type>
        FunctionEq<
            UnorderedListEq<A>,
            UnorderedListEq<A>,
            CompFn<
                UnorderedListEq<A>,
                HomChain<UnorderedList<A>, UnorderedListEq<A>>,
                UnorderedListEq<A>,
                HomChainSingleFn,
                UnorderedListEqReduceFn,
            >,
            IdFn,
        > for UnorderedListEqReduceSingleEq
    {
    }

    impl<A: Type> Groupoid<UnorderedList<A>> for UnorderedListEq<A> {}

    #[derive(Clone)]
    pub struct UnorderedListEqItem<A: Type> {
        pub left_idx: usize,
        pub right_idx: usize,
        pub eq: A::Eq,
    }

    impl<A: Type> Type for UnorderedListEqItem<A> {
        fn assert_same(a: &Self, b: &Self) {
            assert_eq!(a.left_idx, b.left_idx);
            assert_eq!(a.right_idx, b.right_idx);
            A::Eq::assert_same(&a.eq, &b.eq);
        }

        type Eq = UnorderedListEqItem<A::Eq>;
    }

    impl<A: Type> Family<(UnorderedListEqItem<A>, UnorderedListEqItem<A>)>
        for UnorderedListEqItem<A::Eq>
    {
        type DepFn = UnorderedListEqEqItemDepFn;
    }

    pub struct UnorderedListEqEqItemDepFn;

    impl<A: Type>
        Function<UnorderedListEqItem<A::Eq>, (UnorderedListEqItem<A>, UnorderedListEqItem<A>)>
        for UnorderedListEqEqItemDepFn
    {
        fn call(
            eq_item: UnorderedListEqItem<A::Eq>,
        ) -> (UnorderedListEqItem<A>, UnorderedListEqItem<A>) {
            let (left_eq, right_eq) =
                <<A::Eq as Type>::Eq as Family<(A::Eq, A::Eq)>>::DepFn::call(eq_item.eq);
            (
                UnorderedListEqItem {
                    left_idx: eq_item.left_idx,
                    right_idx: eq_item.right_idx,
                    eq: left_eq,
                },
                UnorderedListEqItem {
                    left_idx: eq_item.left_idx,
                    right_idx: eq_item.right_idx,
                    eq: right_eq,
                },
            )
        }

        type EqFn = TodoFn;
    }

    impl<A: Type> Relation<UnorderedListEqItem<A>> for UnorderedListEqItem<A::Eq> {}

    impl<A: Type> Category<UnorderedListEqItem<A>> for UnorderedListEqItem<A::Eq> {
        type Inv = bool;

        type ReduceFn = UnorderedListEqEqItemReduceFn;

        type ReduceSingleEq = TodoFn;
    }

    pub struct UnorderedListEqEqItemReduceFn;

    impl<A: Type>
        Function<
            HomChain<UnorderedListEqItem<A>, UnorderedListEqItem<A::Eq>>,
            UnorderedListEqItem<A::Eq>,
        > for UnorderedListEqEqItemReduceFn
    {
        fn call(
            chain: HomChain<UnorderedListEqItem<A>, UnorderedListEqItem<A::Eq>>,
        ) -> UnorderedListEqItem<A::Eq> {
            let (start, items) = chain.into_parts();
            UnorderedListEqItem {
                left_idx: start.left_idx,
                right_idx: start.right_idx,
                eq: reduce(HomChain::new(
                    start.eq,
                    items
                        .into_iter()
                        .map(|item| HomChainItem {
                            hom: item.hom.eq,
                            inv: item.inv,
                        })
                        .collect(),
                )),
            }
        }

        type EqFn = TodoFn;
    }

    impl<A: Type>
        FamilyFunction<
            (UnorderedListEqItem<A>, UnorderedListEqItem<A>),
            HomChain<UnorderedListEqItem<A>, UnorderedListEqItem<A::Eq>>,
            UnorderedListEqItem<A::Eq>,
        > for UnorderedListEqEqItemReduceFn
    {
    }

    impl<A: Type>
        RelationFunction<
            UnorderedListEqItem<A>,
            HomChain<UnorderedListEqItem<A>, UnorderedListEqItem<A::Eq>>,
            UnorderedListEqItem<A::Eq>,
        > for UnorderedListEqEqItemReduceFn
    {
    }

    impl<A: Type> Groupoid<UnorderedListEqItem<A>> for UnorderedListEqItem<A::Eq> {}
}

#[test]
fn unordered_list_eqs() {
    let list_eq = UnorderedListEq::new(UnorderedList(vec![
        UnorderedListEqItem {
            left_idx: 1,
            right_idx: 2,
            eq: SetEq(42),
        },
        UnorderedListEqItem {
            left_idx: 2,
            right_idx: 0,
            eq: SetEq(43),
        },
        UnorderedListEqItem {
            left_idx: 0,
            right_idx: 1,
            eq: SetEq(44),
        },
    ]));
    let (left, right) = dep(&list_eq);
    UnorderedList::assert_same(&left, &UnorderedList(vec![44, 42, 43]));
    UnorderedList::assert_same(&right, &UnorderedList(vec![43, 44, 42]));

    let left_refl = refl(left.clone());
    let (left_refl_left, left_refl_right) = dep(&left_refl);
    UnorderedList::assert_same(&left_refl_left, &left);
    UnorderedList::assert_same(&left_refl_right, &left);

    let list_eq_inv = inv(list_eq.clone());
    let (inv_left, inv_right) = dep(&list_eq_inv);
    UnorderedList::assert_same(&inv_left, &UnorderedList(vec![43, 44, 42]));
    UnorderedList::assert_same(&inv_right, &UnorderedList(vec![44, 42, 43]));
    // Note: The order of items is an artifact of `UnorderedListEqReduceFn`.
    UnorderedListEq::assert_same(
        &list_eq_inv,
        &UnorderedListEq::new(UnorderedList(vec![
            UnorderedListEqItem {
                left_idx: 0,
                right_idx: 2,
                eq: SetEq(43),
            },
            UnorderedListEqItem {
                left_idx: 1,
                right_idx: 0,
                eq: SetEq(44),
            },
            UnorderedListEqItem {
                left_idx: 2,
                right_idx: 1,
                eq: SetEq(42),
            },
        ])),
    );

    let list_eq_inv_inv = inv(list_eq_inv);
    let (inv_inv_left, inv_inv_right) = dep(&list_eq_inv_inv);
    UnorderedList::assert_same(&inv_inv_left, &left);
    UnorderedList::assert_same(&inv_inv_right, &right);
    // Note: The order of items is an artifact of `UnorderedListEqReduceFn`.
    UnorderedListEq::assert_same(
        &list_eq_inv_inv,
        &UnorderedListEq::new(UnorderedList(vec![
            UnorderedListEqItem {
                left_idx: 0,
                right_idx: 1,
                eq: SetEq(44),
            },
            UnorderedListEqItem {
                left_idx: 1,
                right_idx: 2,
                eq: SetEq(42),
            },
            UnorderedListEqItem {
                left_idx: 2,
                right_idx: 0,
                eq: SetEq(43),
            },
        ])),
    );

    let inv_inv_eq = inv_inv_eq(list_eq.clone());
    let (inv_inv_eq_left, inv_inv_eq_right) = dep(&inv_inv_eq);
    UnorderedListEq::assert_same(&inv_inv_eq_left, &list_eq_inv_inv);
    UnorderedListEq::assert_same(&inv_inv_eq_right, &list_eq);
    // Note: The order of items is an artifact of `UnorderedListEqReduceFn`.
    UnorderedListEq::assert_same(
        &inv_inv_eq.0,
        &UnorderedListEq::new(UnorderedList(vec![
            UnorderedListEqItem {
                left_idx: 0,
                right_idx: 2,
                eq: UnorderedListEqItem {
                    left_idx: 0,
                    right_idx: 1,
                    eq: SetEq(SetEq(44)),
                },
            },
            UnorderedListEqItem {
                left_idx: 1,
                right_idx: 0,
                eq: UnorderedListEqItem {
                    left_idx: 1,
                    right_idx: 2,
                    eq: SetEq(SetEq(42)),
                },
            },
            UnorderedListEqItem {
                left_idx: 2,
                right_idx: 1,
                eq: UnorderedListEqItem {
                    left_idx: 2,
                    right_idx: 0,
                    eq: SetEq(SetEq(43)),
                },
            },
        ])),
    );
}
