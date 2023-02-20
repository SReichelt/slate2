# Confluence

This document collects issues related to confluence, and explores different solutions for each.

## Symmetry of equality

The following three desirable properties imply that `a = b ≡ b = a` for all `a`,`b`.

1. `symm (refl a) ≡ refl a` for all `a`.
2. `a =[refl A] b ≡ a = b` for all `A`,`a`,`b`.
3. `b =[symm e] a ≡ a =[e] b` for all `e`,`a`,`b`.

Of these three properties, the second is probably the most important, since its failure would imply
that `ap` is not simply a special case of `apd`. It is also hard to imagine a definition of
dependent equality where it does not hold.

The third property is more or less unavoidable if dependent equality is defined as the relation
underlying type equivalence, as `symm` on a type equivalence will always swap the relation. A
"one-sided" definition of dependent equality breaks the property but results in suboptimal terms,
and may also cause confluence problems on its own.

Giving up the first seems reasonable, but potentially leads to confluence problems with the constant
combinator (see below); its definition of `ap` probably needs to reduce to an `arbitrary` value
between `refl b` and `symm (refl b)`.

Making equality definitionally symmetric may not be quite as impossible as it sounds. For `Pi` and
`Sigma`, the symmetry would propagate through their definitions of equality. The only problem is
type equivalence, and in particular the relation of type `A → B → U` when `A = B`, which cannot
really be definitionally equal to a relation of type `B → A → U`. (It would imply that those two
function types are also definitionally equal, which would require some fundamental built-in
argument-swapping mechanism that we definitely don't want.)

A solution may be that equality of types is not directly defined as type equivalence, but as an
`arbitrary` point between `Equiv A B` and `Equiv B A`, which are equal. While this would be a bit
annoying to work with because we could not even extract `to` and `inv` functions from an equality,
we can lift operations on elements to operations on `arbitrary` values, and therefore operations on
equivalences to operations on equalities.

However, even if equality is definitionally symmetric for all individual types, that does not make
equality definitionally symmetric _in general_, i.e. we cannot apply an argument of type `a = b` to
a function taking `b = a`. Unfortunately, that is exactly what can happen if the three properties
listed above hold. Obviously, this cannot be handled via reduction. Instead, when checking whether
two expressions are definitionally equal, we would have to take this special property of equality
into account (which seems doable).

A good alternative may be to have both a directed and an undirected version of equality, where the
undirected version is defined using `arbitrary` as described for `Equiv` above. The main difficulty
with this solution will probably be how to make the undirected equality reduce as desired, as
`arbitrary` itself typically cannot be reduced. Another possible catch is that for the undirected
equality to actually be symmetric, `arbitrary` needs to take an undirected equality as an argument,
making its type recursive in a way that seems risky. Quite possibly, support for symmetry is
actually a fundamental property of the type theory that cannot be attained by adding constants and
reduction rules.

## Transitivity of type equivalence

If we can extract a relation from a type equivalence `e : Equiv A B` (and that relation is not
simply defined to be `λ a b. to e a = b`), an important question is how the relation should be
defined for `trans e f`.

The obvious variant, which uses an instance of `Sigma`, has the problem that `refl` cannot be
definitionally eliminated on either side, as that would require the `Sigma` instance to be
definitionally equal to something that is not a `Sigma` instance. Unfortunately, not being able to
eliminate `refl` would have wide-ranging consequences, not just in terms of usability but also for
confluence of combinators.

It is possible to "flatten" the relation to a function on either side, and to define the relation
for `trans` as a composition of a relation and a function. This recovers the original relation if
the "flattened" side is `refl`, but introduces the difficulty of having two different versions of
`trans`.

Possibly there is a solution that keeps the relation abstract in the general case, but recovers the
original relation if either side is `refl`. Alternatively, we may not want to preserve any exact
relation at all, but only via `arbitrary`. It is not clear yet whether we can eliminate `refl` in
that case, but it seems plausible.

Another possibility may be to avoid defining an exact relation at all for any type equivalence
(except `refl`), making that relation available only via `arbitrary`. 

## Combinators

Some lambda terms can be converted to combinators in different ways, for example `λ a. f b` where
neither `f` nor `b` depend on `a` may be regarded either as a constant or as an application.
Conversion to combinators may happen at different points during reduction alternatives, so matches
on combinators must be confluent with respect to such alternatives.

The different possible conversions are given by the five extensionality axioms for combinators. The
most complex one of those is associativity of the S combinator, which corresponds to the following
two terms being definitionally equal by beta reduction (where `g`, `f`, and `b` may depend on `x`):
* `λ x. g (f b)`
* `λ x. (λ y. g (f y)) b`

The problem is that the two terms above are converted to combinators entirely differently, but
since they are definitionally equal, the result of `ap` must be as well. This requires essentially
all definitional equalities about `trans` that one could possibly want.
