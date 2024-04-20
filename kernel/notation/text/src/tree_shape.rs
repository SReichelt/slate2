use std::{
    fmt::Debug,
    ops::{Add, AddAssign, Sub, SubAssign},
};

use crate::{type_list::*, type_list_trait};

pub trait LimitedIndex:
    Copy + Debug + PartialOrd + Default + Add + AddAssign + Sub + SubAssign + 'static
{
    fn max_idx() -> usize;

    fn from_usize(idx: usize) -> Self;
    fn to_usize(idx: Self) -> usize;
}

macro_rules! limited_index {
    ($ty: tt) => {
        impl LimitedIndex for $ty {
            fn max_idx() -> usize {
                $ty::MAX as usize
            }

            fn from_usize(idx: usize) -> Self {
                debug_assert!(idx <= Self::max_idx());
                idx as $ty
            }

            fn to_usize(idx: Self) -> usize {
                idx as usize
            }
        }
    };
}

limited_index!(u8);
limited_index!(u16);
limited_index!(u32);
limited_index!(usize);

type_list_trait!((TreeShape: SizedTypeList + 'static) (: LimitedIndex) [
    (MatchTreeShape),
    (MatchTreeShapeIndex: Copy + PartialOrd + Default),
]);

impl<T: Copy + PartialOrd + Default> MatchTreeShapeIndex for TupleConstructor<T> {
    type MatchEmpty = T;
    type MatchNonEmpty<Head: LimitedIndex, Tail: Copy + PartialOrd + Default> = (Head, Tail);
}

pub type TreeShapeIndex<Shape, T> = <Shape as TreeShape>::MatchTreeShapeIndex<TupleConstructor<T>>;

pub trait TreeStorageDesc: MatchTreeShape {
    fn children<Idx: LimitedIndex, Child>(node: &Self::MatchNonEmpty<Idx, Child>) -> &[Child];

    fn children_mut<Idx: LimitedIndex, Child>(
        node: &mut Self::MatchNonEmpty<Idx, Child>,
    ) -> &mut [Child];
}
