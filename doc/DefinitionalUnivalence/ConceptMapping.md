# Attempt 1

One of the fundamental properties of the logic presented here is that certain concepts of lambda
calculus and type theory are considered to be "derived". In theory, they could indeed be implemented
by mapping them to other, more fundamental concepts, but in reality the impact on performance and
complexity would be too large. Instead, the implementation follows an "as if" rule.

The following mappings exist.

* Lambda abstractions and variables → combinators.

  As a result, the only primitive terms are constants and applications.

  Beta reduction at the top level is implemented by the obvious reduction rule of each combinator.

  Reduction under lambda abstractions cannot be implemented with a finite number of rules of this
  form. Instead, we need to add the rule that every term `f` that has a function type may be
  reduced by temporarily introducing a variable `a`, reducing the term `f a` (potentially
  recursively), and abstracting the result over `a`.

* Type formers → constants.

  Thus, a type is the same as a term of type `U`, where `U` is a particular constant.

  The type of a lambda abstractions is given by an appropriate application of the `Pi` constant;
  however, since lambda abstractions are not fundamental, this is implied by the typing of
  combinators. The type of an application is determined by applying the function argument to the
  argument of `Pi` belonging to the function.

* Reduction rules → equality.

  In particular:
  * A reduction rule with variables is mapped to a universally quantified equality, i.e. a `Pi`
    type.
  * The constant that witnesses reduction within a function argument is `ap`. 
  * The constant that witnesses reduction within the corresponding function is given by the
    reduction rule of equality of functions.
  * Reduction under a lambda abstraction corresponds to function extensionality.
  * The elimination of reduction rules causes terms to no longer be definitionally equal; this
    also applies to types in particular. Whenever the nominal type of a term `a` is `A` but a type
    check `a : B` previously succeeded due to `B` being definitionally equal to `A`, an explicit
    cast along the equality `eAB : A = B` must be inserted, i.e. we have `to eAB a : B` instead of
    `a : B`.
    Casts must be constructed _before_ eliminating reduction rules, to prevent failures of other
    type checks during the construction of casts.
  * The insertion of casts may cause other type checks to fail, in particular because we frequently
    face a choice whether to cast a function or its input and/or output. This should always be
    solvable by inserting casts manually instead, but may be inconvenient.
  * Proving the equality of two expressions that involve casts may require proving that the
    arguments of casts are equal, i.e. we expect to frequently encounter proofs that equalities are
    equal. This is roughly related to confluence of the original reduction rules, and will hopefully
    manifest as confluence up to equality.

# Attempt 2

We start with our target type theory with built-in telescopes, parameterized definitions, type
expressions that include inductive types, and terms that include match expressions.
This type theory is equivalent to intensional type theory with universes. We add an equality type
with reflexivity plus type-specific extra constructors that implement univalence.

The goal is to interpret many built-in concepts with a finite number of instances of the same
concepts, so that we can prove properties of these instances, and/or reinterpret them individually.
Each mapping consists of the necessary definitions and an algorithm to convert between the original
and interpreted versions. This algorithm will be executed on demand.

* Telescopes.

  The main specialty of our custom telescopes is that argument kinds must match the corresponding
  parameter kinds exactly, i.e. parameter and argument kinds are a meta-level concept.

  Each parameter is recursively parameterized by a telescope, which is considered part of the
  parameter kind (and will often be empty). Arguments for the telescope must be supplied when
  accessing the variable, analogously to referencing a parameterized definition. The argument kind
  contains a suitable argument parameterized by the (appropriately substituted) telescope.

  The inner part of the parameter kind can be either a type expression (so that the parameter
  introduces an instance variable) or "type" (so that the parameter introduces a type variable).
  The argument kind follows this distinction.

  The interpretation of telescopes requires multiple steps, the first of which is the introduction
  of a type of types (i.e. a single universe, which is distinct from a generalized concept of
  universes). This can be constructed as an inductive type analogously to the set of cardinal
  numbers in HLM, in particular using a match expression to extract the type variable. Then, all
  type variables can be interpreted as terms of this particular type.

  Every typed object parameterized by a telescope can be interpreted as an unparameterized object
  with a nested (dependent or independent) function type. In particular, this applies to
  parameterized parameters; constructors and definitions are handled below.
  Arguments are mapped to function application, which is a definition.

  We probably want the independent function type to be a definition that specializes the dependent
  function type.

* Inductive types.

  Flat inductive types are simply interpreted as dependent pairs and disjoint unions (and unit and
  empty types), after parameterized parameters have been replaced by functions. This also replaces
  constructor applications and match expressions, except that all primitive types mentioned so far
  (including the type of types and the type of dependent functions) remain unaffected.

  Actual induction and recursion requires conversion into some fixpoint variant, with careful
  treatment of definitional equality. We do not need this at the beginning.

* Definitions.

  Parameterized definitions can mostly be converted to functions, unless induction or recursion is
  involved. In particular, type constructors become function applications.

  Moreover, non-recursive definitions can be inlined.

* Function constructor.

  Combinators are simply specific instances of the function constructor. An instance of the function
  constructor can be converted to combinators if all of its contents have been converted to function
  applications.

  TODO: This should allow us to do a sort of induction over combinators, given appropriate
  equalities for all ambiguous cases.

* Induction over type constructors.

  * Connection to type of universes?
  * Makes equality definable?

* Definitional equality.

  Every particular definitional equality can be interpreted as rewriting along a particular instance
  of reflexivity, given that rewriting a term along reflexivity is expected to yield the original
  term definitionally. This requirement seems to introduce a kind of recursion, which we expect to
  lead to the extensionality axioms for combinators.

* Equality constructors.

  We wish to treat equality on a specific type similarly to an inductive type that supports
  construction and matching. This way, we avoid making equality definitionally equal to equivalence
  but can still convert easily in both directions.

  TODO
