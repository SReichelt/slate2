# Notation in Slate 2

This document describes parsing and printing in Slate 2. Many details are still work in progress.

Goals:
* Most aspects of the language should be general-purpose instead of being designed for a particular
  mathematical logic. In particular, the structure of the resulting abstract syntax tree should be
  configurable.
* It should be possible to parse input without executing additional code outside of the parser.
  (The distinction between code and non-code is admittedly a bit blurry; it is mostly a matter of
  complexity rather than e.g. Turing-completeness.)
* Forward references should be possible, even to symbols that introduce custom notations.
* We want to enable as much standard mathematical notation as possible under the first three
  constraints.
* Every print/parse cycle must round-trip reliably. (This implies that ambiguity is only allowed in
  cases where it can be resolved by inserting parentheses.)

To achieve these goals, the syntax is split into multiple layers, each of which adds more structure.
This can be regarded as an extension of the traditional distinction between tokenization and
parsing.

Some layers may be combined when parsing, but several passes are definitely necessary due to data
obtained from forward references.

## Tokenization

Similarly to most programming languages, but unlike e.g. Lean, Slate 2 has a rigid token structure.
However, most mathematical symbols are not individual tokens but form identifiers. The list of
tokens is as follows.

* Parenthesis characters, including many non-ASCII parentheses, vertical lines, and special
  quotation symbols.
* Punctuation, limited to `.,;`. Note that a dot may be part of a number; see below. Moreover,
  multiple dots directly following each other are treated equivalently to a keyword.
* Keywords, which consist of the character `%` possibly followed by an unquoted identifier as
  defined below.
* Numbers, which can either start with an ASCII numeral or with a dot. A number starting with an
  ASCII numeral can contain ASCII alphanumeric characters or underscores, followed by an optional
  dot which can be followed by more ASCII alphanumeric characters as well as `+` or `-` if preceded
  by `e` or `E`. A number starting with a dot must be followed by an ASCII numeral and can only
  follow a non-dot punctuation character, an opening parenthesis, a number (but not immediately), or
  an unquoted identifier ending with a symbol (see below), possibly separated by whitespace.
  Afterwards, the same rules apply as for the part of a number following a dot.
  A number cannot follow a dot which is a punctuation symbol, even when separated by whitespace.
* String literals surrounded by single or double quotes. These literals may contain the same escape
  sequences as Rust, and any character except ASCII control characters (which includes line breaks).
  (The backtick character is reserved for future use.)
* Quoted identifiers, which consist of the character `@` followed by a string in double quotes.
* Unquoted identifiers, consisting of groups of either symbols or alphanumeric characters, but not
  both. The two types of characters can potentially span the entire unicode range, but we treat
  uncategorized characters as alphanumeric. Underscores, apostrophes, and quotation marks are
  allowed everywhere in identifiers, except that an unquoted identifier cannot start with an
  apostrophe. These three characters can be used to connect groups of identifiers and symbols. An
  unquoted identifier cannot start with `%` or `@`, or contain any of the parenthesis or punctuation
  characters mentioned above, nor whitespace, ASCII control characters, or backticks. An identifier
  cannot start with a numeral, except when the identifier follows a dot (possibly with whitespace
  between).
  An unquoted identifier starting with `:` is called a "definition symbol" and treated equivalently
  to a keyword.

Tokens may be separated by whitespace and comments. Line comments start with `//`; block comments
start with `/*` and end with `*/`, and may be nested. Therefore, unquoted identifiers are not
allowed to start with `//` or `/*`. (The use of these character sequences at other positions within
identifiers is allowed but discouraged.)

## Parenthesis Matching

Each parenthesis character that has a clear "opening" and "closing" variant must appear in pairs,
resulting in a token tree. In subsequent layers, the entire range from an opening to its closing
parenthesis is regarded as a single token.

(Since this rule does not apply to vertical lines, notation like `|x|` requires additional
parentheses in contexts where the left vertical bar may also be regarded as a delimiter. Moreover,
the requirement rules out certain particular notation like `]x[` or `[0,1)`.)

## Parameter Identification

A parameter generally serves two functions.
* It has a certain _scope_, in which the parameter can be referenced using its name or more
  generally its notation.
* If it is part of a surrounding entity that can be referenced, then such a reference contains an
  _argument_ for the parameter (which may, however, be empty for a given type of parameter).

We reserve a fixed basic syntax for all parameters, so that we can handle references and arguments
fairly generically.

At top level, each document consists of a header followed by a series of global parameters (which
are usually definitions). Both the header and each parameter are delimited by `;`. The header
must be the keyword `slate` followed by the name of a _metamodel_ (roughly analogous to a schema)
for the document.

The metamodel specifies other locations where parameters may occur. We distinguish between two
general cases.

* There may be an arbitrary number of _parameterizations_, each of which reserves a specific pair
  of parentheses (such as `[]`) at four locations:
  * after an opening parenthesis,
  * after a comma,
  * after a semicolon, or
  * after another parameterization.

  The pair of parentheses encloses a group of parameters separated by `;`. The scope of each
  parameter extends from the next parameter (if any) to the next outer semicolon or closing
  parenthesis.

* In addition, there may be an arbitrary number of _objects_, each of which reserves a specific pair
  of parentheses at every location except following a dot. The syntax for parameters within these
  parentheses is the same as above, except that the list of parameters may be delimited by a
  specified vertical line character. However, the parameters defined within an object are never
  directly in scope.

Each individual parameter consists of the following, in series.
* Optionally an additional parameterization, as described above.
* The name or more generally the notation of the parameter, or of several parameters separated by
  `,`.
* The data of this parameter (or these parameters, respectively), which must start with either a
  definition symbol or a keyword, or be empty. (We will write this as `: ...` below.)

For example, if parameterization with `[]` is defined in the metamodel, the following are some
possible lists of parameters.
* `[x : ...]` declares one parameter `x`.
* `[x : ...; y : ...]` declares two parameters `x` and `y`.
* `[x,y : ...]` declares two parameters `x` and `y` that have the same data.
* `[[x : ...] f(x) : ...]` declares a parameter `f` that is additionally parameterized by `x`, i.e.
  a second-order parameter, in function notation.
* `[[x : ...] f(x),g(x) : ...]` declares two parameters `f` and `g` that are additionally
  parameterized by `x`.
* `[[a,b : ...] a + b : ...]` declares a parameter `+` that is additionally parameterized by `a`
  and `b`, in infix notation.
* In principle, this scheme may be continued recursively, but parameterizations must be included in
  the notation. E.g. `[[[x : ...] f(x) : ...] g([x] f(x)) : ...]` declares a third-order parameter
  `g`; `[[[[x : ...] f(x) : ...] g([x] f(x)) : ...] h([[x] f(x)] g([x] f(x))) : ...]` declares a
  fourth-order parameter `h`.

The notation expression of a (potentially additionally parameterized) parameter is recursively any
of the following.
* An identifier.
* A sequence of notation expressions.
* A comma-separated list of notation expressions surrounded by a chosen pair of parentheses or
  vertical lines, unless that pair of parentheses has been reserved by the metamodel.
  * If a pair of parentheses is reserved for parameterization, then it cannot be used at the
    beginning of a notation expression of a local or global parameter, or inside a notation at a
    location where parameterization is permitted.
  * If a pair of parentheses is reserved for an object, then it cannot be used in a notation
    expression, except at the beginning of the notation of an object parameter.
  * The metamodel may reserve additional pairs of parentheses.
  * The comma-separated list may be empty. A comma after the last list item is ignored in the sense
    that the notation expressions with and without the trailing comma are considered equivalent.
* A reference to one of the additional parameters, identified by a notation expression that is
  equivalent to the notation expression of the parameter. If the parameter is additionally
  parameterized, the reference must be parameterized equivalently, but concrete notations as well as
  data may differ. (It is recommended to use the same notation but to omit data.)
  This alternative takes precedence over all others. However, the entire notation expression is not
  allowed to consist purely of a parameter. Moreover, a notation expression which is parameterized
  or a sequence cannot appear within a sequence.

The syntax for global parameters is identical except for the lack of parentheses and the requirement
to end the last parameter with `;`. Their scope is the entire document.

## Expression Identification

The metamodel specifies where in a document _expressions_ may occur. The defining characteristic of
an expression is that it may be a _variable_, which means that it references a specific parameter
that is in scope at that location.

Whether an expression references a particular parameter is determined by syntactically matching the
expression against the notation expression of the parameter. If the parameter is additionally
parameterized, _arguments_ for (some of) these additional parameters are obtained from the match
result. While the exact format of each argument is specified by the metamodel, the argument of a
parameterized parameter should generally be parameterized equivalently, taking substitutions of
earlier arguments into account.

Arguments for parameters that do not appear in the notation expression are never specified
explicitly.

When there are multiple ways to match an expression against the notation expression of a parameter,
_operator precedence_ and _associativity_ determine which match to use. Both are specified by the
metamodel at the token level; they cannot be overridden by custom notations. If multiple matches are
still possible after taking precedence into account, an error is reported.

In contrast to global and local parameters, parameters within objects cannot be referenced directly
as they lack a scope of their own. Instead, a reference must be prefixed by an expression followed
by a dot. The metamodel defines how to evaluate that expression in order to determine the object in
which to look for the parameter (or alternatively, that the tokens following the dot are not a
reference to an object parameter). The evaluation may require parsing additional files, due to
imports.

To enable object lookup, the expression identification layer must be evaluated in two passes. In the
first pass, expressions are matched against global and local parameters as described above, as well
as against special expression notations defined by the metamodel, but an expression that cannot be
matched (for example because it contains a dot) is not an error. The metamodel specifies how object
lookup is performed on the resulting syntax tree, in a second pass. All expressions must be
identified as such in one of the two passes.

As a consequence, the dot symbol can be regarded as binding more strongly than any other symbol, but
only in cases where a notation expression with that symbol actually exists and is in scope.
Parentheses on either side of the dot may be required to counteract this in certain cases.
(Undesired matches may be reduced by taking into account that an expression cannot start or end with
a dot.)

## AST Building

The next steps are entirely dictated by the metamodel. There are potentially several distinct data
types for expressions, parameters, and arguments. In particular, the data of a parameter often
determines the format of an argument. Additionally, the metamodel may define notations and keywords.

These data structures ultimately determine which expressions are valid at which locations, and how
an abstract syntax tree is constructed from them.

## Type Checking

Type checking operates on the abstract syntax tree and is defined by the metamodel.
