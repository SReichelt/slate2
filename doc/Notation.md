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
* We want every print/parse cycle to round-trip reliably. (This implies that ambiguity is only
  allowed in cases where it can be resolved by inserting parentheses.)

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
* Punctuation, limited to `.,;`. Note that a dot may be part of a number instead; see below.
* The subscript and superscript separator characters `_` and `^`.
* Keywords, which consist of the character `%` possibly followed by an unquoted identifier as
  defined below.
* Numbers, which can either start with an ASCII numeral or with a dot. A number starting with an
  ASCII numeral can contain ASCII alphanumeric characters or underscores, followed by an optional
  dot which can be followed by more ASCII alphanumeric characters as well as `+` or `-` if preceded
  by `e` or `E`. A number starting with a dot must be followed by an ASCII numeral and can only
  follow a non-dot punctuation character, an opening parenthesis, a number (but not immediately, and
  not if the number ends with a dot), or an unquoted identifier consisting of symbol characters (see
  below), possibly separated by whitespace. Afterwards, the same rules apply as for the part of a
  number following a dot.
  A number cannot follow a single dot, even when separated by whitespace. (It becomes an identifier
  then.)
* String literals surrounded by single or double quotes. These literals may contain the same escape
  sequences as Rust, and any character except ASCII control characters (which includes line breaks).
  (The backtick character is reserved for future use.)
* Quoted identifiers, which consist of the character `@` followed by a string in double quotes.
* Unquoted identifiers, consisting of one of the following classes of characters.
  * alphanumeric (which is the default for uncategorized characters),
  * symbols,
  * subscripts, or
  * superscripts.

  An unquoted identifier cannot start with `%` or `@` or the sequence `//` or `/*`, or contain any
  of the parenthesis, punctuation, or subscript/superscript separator characters mentioned above,
  nor whitespace, ASCII control characters, or backticks.
  An unquoted identifier cannot start with a numeral, except when the identifier follows a dot
  (possibly with whitespace between).
  An unquoted identifier can optionally end with any number of apostrophes and quotation marks.
  Quoted and unquoted identifiers are treated equivalently if they consist of the same characters,
  except when explicitly specified otherwise.

Tokens may be separated by whitespace and comments. Line comments start with `//`; block comments
start with `/*` and end with `*/`, and may be nested. Usually, whitespace between tokens has no
syntactic significance other than delimiting the tokens. An exception is that reserved characters
may behave differently depending on whether they are preceded and/or followed by whitespace (not
including comments).

## Parenthesis Matching

Each parenthesis character that has a clear "opening" and "closing" variant must appear in pairs,
resulting in a token tree. In subsequent layers, the entire range from an opening to its closing
parenthesis is regarded as a single element.

Vertical line characters are classified as "opening" or "closing" based on the two adjacent
characters, independently of the tokens that these characters may be part of.

A vertical line is considered a possible opening parenthesis if it is located at the beginning of a
document or preceded by
* whitespace or
* an opening parenthesis (that is not a vertical line) or
* a punctuation or superscript or subscript separator character.

It is considered a possible closing parenthesis if it is located at the end of the document or
followed by
* whitespace or
* a closing parenthesis (that is not a vertical line) or
* a punctuation or superscript or subscript separator character or
* a character classified as subscript or superscript.

It is considered an opening/closing parenthesis if exactly one of the two conditions is satisfied,
and if it is not preceded or followed by itself.

## Parameter Identification

A parameter generally serves two functions.
* It has a certain _scope_, in which the parameter can be referenced using its name or more
  generally its notation.
* If it is part of a surrounding entity that can be referenced, then such a reference may contain an
  _argument_ for the parameter.

Parameters may occur at several different locations; their syntax depends on the type of location.

* The most common syntax is shared by top-level parameters and parameterizations.

  Such parameters can be combined into _groups_, where parameters in a group are given by
  _notation expressions_ as defined below, separated by `,`, and multiple groups can follow each
  other separated by `;`. The last group in a sequence can optionally be delimited by `;` as well.
  The scope of a parameter within a sequence of groups always covers the following groups, but may
  extend further.

  This syntax, which is described in more detail below, is used at three locations.
  * Each document consists of a header followed by a sequence of top-level parameter groups whose
    scope is the entire document (and which are usually "definitions" in some sense). The header and
    the first parameter group (if present) are separated by `;`, equivalently to the separation of
    groups. The header must be the keyword `slate` followed by the name of a _metamodel_ (roughly
    analogous to a schema) for the document.
  * The metamodel specifies zero or more pairs of parentheses that may be used to additionally
    combine parameter groups into _sections_, such that a section may contain zero or more parameter
    groups. A semicolon is required when a section follows a parameter group or the header, but is
    optional at the end of a section.
  * The metamodel also specifies zero or more other pairs of parentheses that may be used for
    _higher-order parameterization_ of parameters. Each parameter group or section may then be
    prefixed by an arbitrary number of these parentheses, each of which contains zero or more
    parameter groups and/or sections. The scope of each higher-order parameter extends from the next
    higher-order parameter group (if any) to the end of the parameterized group or section.

* Moreover, the metamodel specifies zero or more unquoted identifiers as _mapping symbols_, which
  play a role in notation expressions and in unstructured data. Each mapping symbol is specified to
  be either prefix or infix. In both cases, the mapping symbol indicates a _mapping_ which consists
  of a _source_ containing zero or more parameters and a _target_ containing data where those
  parameters are in scope.
  * In the prefix case, source and target are separated by the first `.` following the mapping
    symbol, and the target extends from this `.` until the next comma, semicolon, or closing
    parenthesis (disregarding commas and semicolons that are part of mappings). The source consists
    of zero or more parameters separated by `,`, where each parameter is either a notation
    expression optionally followed by data, or a mapping whose target is a notation expression
    optionally followed by data.
  * In the infix case, the source extends from the previous comma, semicolon, or opening parenthesis
    until the mapping symbol, and the target extends from the mapping symbol until the next comma,
    semicolon, or closing parenthesis. The source must be either a single parameter or a pair of
    specific parentheses specified by the metamodel that encloses zero or more parameters separated
    by `,`. The source cannot be empty; a mapping symbol with an empty source is allowed but does
    not denote a mapping. Each parameter is either a notation expression optionally followed by
    data, or a mapping whose target is a notation expression optionally followed by data. In the
    latter case, parentheses are required around the parameters.

* Finally, the metamodel may reserve zero or more specific pairs of parentheses for _objects_, each
  together with a given vertical line character that will be used as an internal separator (but only
  if it is not considered an opening or closing parenthesis at that location). Whenever these
  parentheses occur in a location that does not play any special role within the parameter
  identification layer, the contents are treated as parameters, called _items_.
  * Each item starts with a notation expression as described below, optionally followed by
    arbitrary data until the next separator character or the end of the object.
  * The separator character may optionally be followed by one or more parameter groups and/or
    sections, which parameterize the item in the sense that their scope extends from the notation
    expression to the separator character. These parameters are again followed by either the
    separator character or the end of the object.
  * Zero or more sections of parameters may follow, delimited by separator characters. The scope of
    the item includes these sections (but the scopes of its parameterizations do not). The item ends
    when two separator characters are placed next to each other. (In particular, this implies that
    unparameterized items cannot contain extra sections.)

A _notation expression_ is recursively any of the following.
* An identifier.
* A subscript or superscript separator.
* A sequence of notation expressions.
* A comma-separated list of notation expressions surrounded by an arbitrary pair of parentheses.
  Whether a given pair of parentheses is allowed depends on reservations made by the metamodel.
  The comma-separated list may be empty. A comma after the last list item is ignored in the sense
  that the notation expressions with and without the trailing comma are considered equivalent.
* If a higher-order parameterization exists, a parameter within that parameterization can be
  referenced using a notation expression that is equivalent to the notation expression of the
  parameter, in the following sense.
  * If the referenced parameter does not have a higher-order parameterization again, the notation
    expression must match exactly.
  * If it does have a higher-order parameterization, then the notation expression must include a
    mapping symbol and be interpretable as a mapping. The number of source parameters of the mapping
    must match the number of higher-order parameters. If one of those higher-order parameters is
    parameterized, the corresponding source parameter must be written as a mapping, such that the
    same rules apply recursively. The mapping target must match the expected notation when the
    matching parameters are substituted.

  This alternative takes precedence over all others. However, the entire notation expression is not
  allowed to consist purely of a parameter. Moreover, a notation expression which is parameterized
  or a sequence cannot appear within a sequence.

A _notation expression_ may optionally be followed by _data_ separated by
* a dot,
* a keyword,
* an unquoted identifier that is reserved for this purpose by the metamodel,
* an opening parenthesis reserved by the metamodel, or
* an infix mapping symbol.

If the notation expression is part of a group, the data ends the group and applies to the entire
group.
A dot, keyword, reserved identifier, or reserved parenthesis is considered a data separator even if
it occurs within parentheses. The data then begins at the previous top-level opening parenthesis.
A parameter group may consist only of data. The metamodel may also specify that _all_ parameter
groups in a section are to be interpreted as data, without requiring a separator.

For example, if the metamodel defines `:` as a notation expression delimiter, higher-order
parameterization with `[]`, and `↦` as an infix mapping symbol, the following are some possible
lists of parameters.
* `x : ...` declares one parameter `x`.
* `x : ...; y : ...` declares two parameters `x` and `y`.
* `x,y : ...` declares two parameters `x` and `y` that have the same data.
* `[x : ...] f(x) : ...` declares a parameter `f` that is additionally parameterized by `x`, i.e.
  a second-order parameter, in function notation.
* `[x : ...] f(x),g(x) : ...` declares two parameters `f` and `g` that are additionally
  parameterized by `x`.
* `[a,b : ...] a + b : ...; [c : ...] -c : ...` declares a parameter `+` that is additionally
  parameterized by `a` and `b`, in infix notation, and a parameter `-` that is additionally
  parameterized by `c`, in prefix notation.
* `[[x : ...] f(x) : ...] g(x ↦ f(x)) : ...` declares a third-order parameter `g`.
* `[[[x : ...] f(x) : ...] g(x ↦ f(x)) : ...] h((x ↦ f(x)) ↦ g(x ↦ f(x))) : ...` declares a
  fourth-order parameter `h`.

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

Parameters within objects are often referenced at locations where they are not directly in scope.
There are two possibilities.
* A reference can be prefixed by an expression followed by a dot. The metamodel defines how to
  evaluate that expression in order to determine the object in which to look for the item (or that
  the tokens following the dot are not a reference to an item). The evaluation may require parsing
  additional files, due to imports.
* At certain locations, the metamodel can determine via a simplified type inference algorithm that
  the expected type is an object. In these cases, items of the object may be referenced without
  qualification.

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
