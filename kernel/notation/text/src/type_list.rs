//! Type lists for variadic metaprogramming.
//!
//! * A type list is represented by either `EmptyTypeList` or `NonEmptyTypeList`, both of which are
//!   zero-size types. Instead of writing these two types directly, use the `type_list!` macro.
//!   (In addition to fixed-length lists, this macro also supports "spread" notation like
//!   `type_list![Type1, Type2, ..Rest]`, which can be useful for matching on type lists of a given
//!   shape.)
//!
//! * A function, type, or trait can be parameterized by a type list by adding a type parameter
//!   constrained to a type list trait. The most generic such trait is `TypeList`, and other traits
//!   represent conditions on the type list items. E.g. `SizedTypeList` encodes the restriction that
//!   each type in the list implements `Sized`.
//!
//! * Users can derive arbitrary traits from `TypeList`. Typically such a trait is implemented for
//!   `type_list![]` and `type_list![Head, ..Tail]` with some conditions on `Head` (corresponding
//!   directly to `EmptyTypeList` and `NonEmptyTypeList`, respectively).
//!   In principle, variadic programming is possible by including functions and/or associated types
//!   in such a trait. However, this tends to obscure the structure of code, because typically one
//!   wants to match on the structure of the type list at the place where it is used as a parameter.
//!   Therefore, the recommended way to derive a type list trait is to use the `type_list_trait!`
//!   macro instead.
//!
//! * The syntax of `type_list_trait!` is
//!   ```
//!   type_list_trait!((TraitName: TraitConstraints) (: ItemConstraints) [
//!       (MatcherName1: MatcherConstraints1),
//!       (MatcherName2: MatcherConstraints2),
//!       ...
//!   ]);
//!   ```
//!   (where item and matcher constraints are optional). This defines a trait `TraitName` which
//!   inherits from `TraitConstraints` (which is required to include `TypeList`), and implements
//!   the trait for all type lists with items matching `ItemConstraints`. In addition, it defines
//!   traits `MatcherName1`, `MatcherName2`, ..., which are typically implemented by user-defined
//!   zero-size types. Each matcher implementation defines two "match result" types, one for an
//!   empty list and one for a nonempty list (parameterized by the head type and the match result of
//!   the tail), such that both types satisfy the specified matcher constraints.
//!   Examples are given below for tuples and enums, and for "combined iterators" in the test code.

use std::{fmt::Debug, marker::PhantomData};

#[derive(Clone, Copy, Debug)]
pub struct EmptyTypeList;

#[derive(Clone, Copy, Debug)]
pub struct NonEmptyTypeList<Head: ?Sized, Tail: TypeList>(PhantomData<Head>, Tail);

#[macro_export]
macro_rules! type_list {
    [] => ($crate::type_list::EmptyTypeList);
    [..$List:ty] => ($List);
    [$Head:ty $(, $($Tail:tt)*)?] =>
        ($crate::type_list::NonEmptyTypeList<$Head, $crate::type_list![$($($Tail)*)?]>)
}

pub(crate) use type_list;

#[macro_export]
macro_rules! type_list_trait {
    (@matcher_trait ($($ItemConstraints:tt)*) $MatcherName:ident $($MatcherConstraints:tt)*) => {
        pub trait $MatcherName {
            type MatchEmpty $($MatcherConstraints)*;
            type MatchNonEmpty<Head $($ItemConstraints)*, Tail $($MatcherConstraints)*> $($MatcherConstraints)*;
        }
    };

    (@matcher_traits $ItemConstraints:tt $(($MatcherName:ident $($MatcherConstraints:tt)*)),*) => {
        $($crate::type_list_trait!(@matcher_trait $ItemConstraints
                                                  $MatcherName $($MatcherConstraints)*);)*
    };

    (($Name:ident $($ListConstraints:tt)*) $(($($ItemConstraints:tt)*))?
     $([$(($MatcherName:ident $($MatcherConstraints:tt)*)),* $(,)?])?) => {
        pub trait $Name $($ListConstraints)* {
            $($(type $MatcherName<M: $MatcherName> $($MatcherConstraints)*;)*)?
        }

        impl $Name for $crate::type_list![] {
            $($(type $MatcherName<M: $MatcherName> = M::MatchEmpty;)*)?
        }

        impl<Head $($($ItemConstraints)*)?, Tail: $Name> $Name for $crate::type_list![Head, ..Tail]
        {
            $($(type $MatcherName<M: $MatcherName> = M::MatchNonEmpty<Head, Tail::$MatcherName<M>>;)*)?
        }

        $crate::type_list_trait!(@matcher_traits ($($($ItemConstraints)*)?)
                                                 $($(($MatcherName $($MatcherConstraints)*)),*)?);
    }
}

type_list_trait!((TypeList: Sized + Debug) (: ?Sized + Debug) [(MatchTypeList: ?Sized)]);
type_list_trait!((SizedTypeList: TypeList) (: Debug) [(MatchSizedTypeList)]);

pub struct TupleConstructor<T>(PhantomData<T>);

impl<T> MatchSizedTypeList for TupleConstructor<T> {
    type MatchEmpty = T;
    type MatchNonEmpty<Head: Debug, Tail> = (Head, Tail);
}

pub type TupleWith<List, T> = <List as SizedTypeList>::MatchSizedTypeList<TupleConstructor<T>>;

// A (nested) tuple containing one instance of each type in the list, i.e. the product of all
// types.
pub type Tuple<List> = TupleWith<List, ()>;

pub struct EnumConstructor<T>(PhantomData<T>);

impl<T> MatchSizedTypeList for EnumConstructor<T> {
    type MatchEmpty = T;
    type MatchNonEmpty<Head: Debug, Tail> = Either<Head, Tail>;
}

#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
pub enum Either<Fst, Snd> {
    Fst(Fst),
    Snd(Snd),
}

pub type EnumWith<List, T> = <List as SizedTypeList>::MatchSizedTypeList<EnumConstructor<T>>;

// A (nested) enum containing an instance of exactly one of the types in the list, i.e. the sum
// of all types.
pub type Enum<List> = EnumWith<List, !>;

#[cfg(test)]
mod tests {
    use std::{
        iter::{self, FusedIterator},
        slice,
    };

    use super::*;

    type_list_trait!((IteratorList: TypeList) (: FusedIterator + Debug) [
        (MatchIteratorList: FusedIterator),
    ]);

    struct CombinedIterConstructor;

    impl MatchIteratorList for CombinedIterConstructor {
        type MatchEmpty = iter::Empty<!>;
        type MatchNonEmpty<Head: FusedIterator + Debug, Tail: FusedIterator> =
            CombinedIter<Head, Tail>;
    }

    struct CombinedIter<Fst: FusedIterator, Snd: Iterator>(Fst, Snd);

    impl<Fst: FusedIterator, Snd: Iterator> Iterator for CombinedIter<Fst, Snd> {
        type Item = Either<Fst::Item, Snd::Item>;

        fn next(&mut self) -> Option<Self::Item> {
            if let Some(fst_item) = self.0.next() {
                Some(Either::Fst(fst_item))
            } else if let Some(snd_item) = self.1.next() {
                Some(Either::Snd(snd_item))
            } else {
                None
            }
        }
    }

    impl<Fst: FusedIterator, Snd: FusedIterator> FusedIterator for CombinedIter<Fst, Snd> {}

    type CombinedIters<List> = <List as IteratorList>::MatchIteratorList<CombinedIterConstructor>;

    #[test]
    fn combined_iter_returns_item_sequence() {
        let mut iter: CombinedIters<type_list![slice::Iter<i32>, slice::Iter<&'static str>]> =
            CombinedIter(
                [1, 2, 3].iter(),
                CombinedIter(["a", "b"].iter(), iter::empty()),
            );
        assert_eq!(iter.next(), Some(Either::Fst(&1)));
        assert_eq!(iter.next(), Some(Either::Fst(&2)));
        assert_eq!(iter.next(), Some(Either::Fst(&3)));
        assert_eq!(iter.next(), Some(Either::Snd(Either::Fst(&"a"))));
        assert_eq!(iter.next(), Some(Either::Snd(Either::Fst(&"b"))));
        assert_eq!(iter.next(), None);
    }
}
