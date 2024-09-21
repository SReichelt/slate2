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

It is possible to combine layers for efficiency when parsing, except that the "expression
identification" layer operates on the completed result of the previous layers.

## Tokenization

Similarly to most programming languages, but unlike e.g. Lean, Slate 2 has a rigid token structure,
although it should be noted that most mathematical symbols are not defined as dedicated tokens but
as identifiers. The list of tokens is as follows.

* Parenthesis characters, including many non-ASCII parentheses, vertical lines, and special
  quotation symbols.
* Punctuation, limited to `.,;`. Note that a dot may be part of a number instead; see below.
* The subscript and superscript separator characters `_` and `^`.
* Keywords, which consist of the character `%` followed by an unquoted alphanumeric identifier as
  defined below.
* Numbers, which can either start with an ASCII numeral or with a dot. A number starting with an
  ASCII numeral can contain ASCII alphanumeric characters or underscores, followed by an optional
  dot which can be followed by more ASCII alphanumeric characters as well as `+` or `-` if preceded
  by `e` or `E`. A number starting with a dot must have an ASCII numeral as its second character,
  and can only follow a non-dot punctuation character, an opening parenthesis, a number (but not
  immediately), an unquoted identifier consisting of symbol characters (see below), or a comment,
  all possibly separated by whitespace. Afterwards, the same rules apply as for the part of a number
  following a dot.
  A number cannot follow a single dot, even if separated by whitespace including comments. An
  alphanumerical character following a dot is regarded as the beginning of an unquoted identifier
  (see below), except in cases where the dot itself is the beginning of a number as described above.
* String literals surrounded by single or double quotes. These literals may contain the same escape
  sequences as Rust, and any character except ASCII control characters (which includes line breaks).
  (The backtick character is reserved for future use.)
* Quoted identifiers, which consist of the character `@` followed by a string in double quotes.
* Unquoted identifiers, consisting of one of the following classes of characters.
  * alphanumeric (which is the default for uncategorized characters),
  * symbols,
  * subscripts, or
  * superscripts.

  An unquoted identifier cannot start with the sequence `//` or `/*`, or contain any of the
  parenthesis, punctuation, or subscript/superscript separator characters mentioned above, nor
  whitespace, ASCII control characters, or backticks.
  An unquoted identifier cannot start with a numeral, except when the identifier follows a dot.
  An unquoted identifier can optionally end with any number of apostrophes and quotation marks.
  Quoted and unquoted identifiers are treated equivalently if they consist of the same characters
  (taking escape sequences into account), except when explicitly specified otherwise.

Tokens may be separated by whitespace and comments. Line comments start with `//`; block comments
start with `/*` and end with `*/`, and may be nested. Usually, whitespace between tokens has no
syntactic significance other than delimiting the tokens. An exception is that reserved characters
may behave differently depending on the preceding and/or following character, regardless of the role
of that character.

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

## Parameter Group Identification

The next three layers are dedicated to locating and analyzing so-called _parameters_, which is a
somewhat misleading term because it also includes all top-level definitions. This layer merely
parses enough structure to locate so-called _parameter groups_, whereas the next two analyze those
parameter groups to determine whether they contain _parameters_ with _notations_ (which are
generalized names).

Locating a parameter group also immediately determines the _scope_ where the parameters will be
visible, and more specifically which other parameter groups in that scope are _parameterized_ by the
group, which is important for notation identification within those groups. This information will be
referred to in later layers, but the parameter identification layer does not need to compute it for
its own purpose.

At the top level, a document consists of a header followed by a sequence of top-level parameter
groups whose scope is the entire document (and which are usually "definitions" in some sense, or
possibly "axioms"). The header must be the keyword `%slate` followed by the name of a _metamodel_
(roughly analogous to a schema) for the document, and then a semicolon. Groups are identified as
follows.

* A parameter group may be a _section_, which is identified by a specific parenthesis pair specified
  by the metamodel. A section contains zero or more parameter groups with the same syntax as
  top-level groups. It may optionally be followed by a semicolon.
  The scope of a parameter within a section is always the same as the scope of the section.

* A parameter group that is not a section ends at the first semicolon (disregarding semicolons
  within parentheses, as noted earlier). This semicolon is mandatory in the sense that the last
  group within a file or section must also end with a semicolon.

* Each group may be _parameterized_ by preceding it with one or more specific parenthesis pairs
  specified by the metamodel. The parameterization contains zero or more parameter groups with the
  same syntax as top-level groups, except that the last group is not required to end with a
  semicolon. Each group within the parameterization may be parameterized again, which is referred to
  as _higher-order parameterization_.

* The metamodel may allow a parameter group to be preceded by an arbitrary number of _prefixes_,
  following the parameterizations (if any). A prefix is an identifier (that is not a prefix mapping
  symbol; see below), a number, or arbitrary tokens surrounded by specific parentheses, followed by
  a dot.

Other than the above, a parameter group may contain arbitrary tokens, including the parentheses
reserved for sections or parameterizations, as long as the group does not start with those
parentheses. However, there are three cases where parameters are identified anywhere within a group.

* The metamodel may decide that a given parenthesis pair should be regarded as a parameterization
  whenever it follows an opening parenthesis, a comma or semicolon within parentheses, a
  _notation delimiter_ as specified in the next section, or another parameterization, and contains a
  notation delimiter.

* The metamodel may declare zero or more specific unquoted identifiers as _mapping symbols_. Each
  mapping symbol is specified to be either prefix or infix. In both cases, the mapping symbol
  indicates a _mapping_ which consists of a _source_ containing zero or more parameters and a
  _target_ where the parameters are in scope. (Note that the additional features of parameter groups
  described above do not apply here.)

  * In the prefix case, source and target are separated by the first `.` following the mapping
    symbol, disregarding dots that are part of other mappings, and the target extends from this dot
    until the next comma, semicolon, or closing parenthesis, disregarding commas that are part of
    other mappings. The source consists of zero or more parameters separated by `,` and otherwise
    consisting of arbitrary tokens except `;`, again disregarding commas that are part of other
    mappings. (Note that this implies that the mapping is invalid if there is no dot between the
    mapping symbol and the next closing parenthesis or semicolon.)

  * In the infix case, the source extends from the previous comma, semicolon, or opening parenthesis
    until the mapping symbol, and the target extends from the mapping symbol until the next comma,
    semicolon, or closing parenthesis, always disregarding commas that are part of other mappings.
    The source must be either a single parameter consisting of arbitrary tokens except `,` and `;`,
    disregarding commas that are part of other mappings, or a specific parenthesis pair specified by
    the metamodel that encloses zero or more parameters separated by `,`. The source cannot be
    empty; a mapping symbol with an empty source is allowed but does not denote a mapping.

* Moreover, the metamodel may reserve specific parenthesis pairs for _objects_. For each such pair,
  the metamodel also specifies a vertical line character that will be used as an internal separator
  (but only if it is not considered an opening or closing parenthesis at that location).

  An object is split into zero or more _items_ which are separated by two consecutive occurrences of
  the separator character. Within each item, the separator character delimits one or more parts, the
  first two of which play a special role (when present).
  * The first part contains a parameter consisting of arbitrary tokens except for `;` and the
    separator character. Its scope includes all parts except the first two.
  * The second part, if present, contains one or more parameter groups which follow the same rules
    as parameterizations of top-level parameters, except that they cannot contain the vertical
    separator character (unless surrounded by a section). The parameter groups parameterize the
    first part.

## Parameter Notation Identification

Within each parameter or group identified by the previous layer, the metamodel specifies how to
extract a _notation expression_ for each parameter. In a group, this is given by a collection of
unquoted identifiers, keywords, or parentheses, each of which terminates the list of parameter
notations, resulting in the preceding tokens to be interpreted as notation expressions separated by
`,`. As an exception, if a string or a keyword that is _not_ in the collection appears before the
terminating token, the group is regarded as having no parameters.

The notation expression of a single parameter that is not part of a group may either be terminated
by a token from the same list, or covers the entire parameter if no such token is present.

If a parameter group has at least one prefix, it must contain exactly one parameter, and special
rules apply regarding parentheses around the notation expression of that parameter.
* The notation _may_ always be surrounded by the same parentheses as those used for prefixes, and
  those parentheses are ignored unless omitting them would render the notation expression invalid.
* The notation _must_ be surrounded by those parentheses if it contains more than one identifier
  or number in sequence at top level.

## Parameter Notation Analysis

Notation expressions have specific semantics that are later used when matching other expressions
against them. Analyzing a notation expression requires taking into account the notation expressions
of all parameters parameterizing it.

The process of analyzing a notation expression abstracts over the following details.

* If any subsequence of tokens matches a notation expression found within the parameterization, then
  this part of the notation is considered to refer to that parameter instead of the literal sequence
  of tokens. In particular, the word "match" in the previous sentence must take this generalization
  into account for higher-order parameterizations. Overlapping matches that cause ambiguities are
  considered errors, and moreover a notation expression cannot consist entirely of a single
  parameter reference.

* For every mapping within the notation expression, each source parameter is abstracted as follows.
  * Only the notation of the source parameter is considered part of the surrounding notation; the
    tokens following the notation are not.
  * If the source parameter does not contain any mapping symbols, then it may be replaced with an
    arbitrary notation expression when substituting the parameter within the target accordingly.
  * Otherwise, this only applies to the target(s) of mapping symbol(s) within the source parameter,
    taking into account all other abstraction rules. (In particular, the source of a mapping within
    the source parameter may again be replaced with another expression while performing the same
    replacement in the target.)

* For an infix mapping with a single parameter, the variants with and without parentheses around the
  source are considered equivalent.

* A comma or semicolon before a closing parenthesis is considered "ignorable" in the sense that two
  expressions that only differ by a comma or semicolon before a closing parenthesis are considered
  equivalent. Multiple consecutive commas or semicolons are not allowed, and neither is a single
  comma or semicolon surrounded by parentheses.

* Quoted and unquoted identifiers are equivalent if the resulting string contents are equal.

* Numbers are treated as unquoted identifiers.

Keywords and strings are not allowed within (the non-ignored parts of) notation expressions, and
dots are only allowed as part of mappings.

For example, if the metamodel defines `:` as a notation expression delimiter, parameterization with
`[]`, and `↦` as an infix mapping symbol, the following are some possible lists of parameters.
* `x : ...` declares one parameter `x`.
* `x : ...; y : ...` declares two parameters `x` and `y`, each within their own group.
* `x,y : ...` declares two parameters `x` and `y` in a single group.
* `[x : ...] f(x) : ...` declares a parameter `f(_)`, where the underscore can match any expression.
* `[x : ...] f(x),g(x) : ...` declares two parameters `f(_)` and `g(_)`.
* `[a,b : ...] a + b : ...; [c : ...] -c : ...` declares a parameter `_ + _` and a parameter `-_`.
* `[[x : ...] f(x) : ...] g(x ↦ f(x)) : ...` declares a parameter `g(_ ↦ _)`. Note how the target of
  the mapping can be an arbitrary expression because `f(x)` is abstracted to refer to the parameter
  with that notation.
* `[[x : ...] f(x) : ...] g(y ↦ f(y)) : ...` actually declares the same parameter, `g(_ ↦ _)`, due
  to how `f(x)` is abstracted. (A warning is recommended in such cases.)
* `[[[x : ...] f(x) : ...] g(x ↦ f(x)) : ...] h((x ↦ f(x)) ↦ g(x ↦ f(x))) : ...` declares a
  parameter `h((_ ↦ _) ↦ _)`.

## Expression Identification

In the expression identification layer, all previously unidentified data is interpreted as specified
by the metamodel. For a given sequence of tokens, there are a few possibilities:
* The metamodel can directly interpret the sequence, possibly yielding subsequences that must be
  interpreted further.
* It can specify that the sequence is an _expression_ that may reference a local or global
  parameter that is in scope.
* Alternatively or in addition, it can specify that the sequence may reference an object item of a
  specific object.
* Alternatively, it can specify that the sequence may reference a parameter of a specific object
  item.
* Finally, if an expression did not match any parameter, the metamodel can choose to interpret it
  directly again. (Two common examples are parentheses around the entire expression, and expressions
  containing dots, where the left-hand and right-hand sides of a dot must be interpreted
  individually.)

Whether a sequence of tokens references a particular parameter or object item is determined by
matching its tokens against the notation expression of the parameter/item. If the parameter/item is
additionally parameterized, parameter references within the notation can be matched with almost
arbitrary sequences of tokens, except that
* such sequences cannot contain top-level commas or semicolons, and
* if multiple parameter references directly follow each other in the notation expression, all
  parameters except the first must be matched with exactly one token (which may be a group of tokens
  surrounded by parentheses).

If there are multiple ways to match the tokens against one or more notation expressions, possible
matches are first reduced according to two rules.
* If the explicitly matched tokens of one match are a strict superset of the explicitly matched
  tokens of another match (where "tokens" refers to the specific items within the sequence), then
  the first match is always preferred over the second.
* In cases where the explicitly matched tokens of two or more matches are the same, local parameters
  are always preferred over global parameters, and inner scopes are preferred over outer scopes.

The metamodel then chooses a match among those that remain, or none, e.g. according to operator
precedence and associativity rules.

If the sequence of tokens is interpreted directly by the metamodel, but a subsequence is found to
reference a parameter, then the interpretation of another subsequence may depend on the
interpretation of the data of that parameter, including recursively (as long as the recursion does
not involve the parameter being interpreted).

## AST Building

The next steps are entirely dictated by the metamodel. There are potentially several distinct data
types for expressions, parameters, and arguments. In particular, the data of a parameter often
determines the format of an argument. Additionally, the metamodel may define notations and keywords.

These data structures ultimately determine which expressions are valid at which locations, and how
an abstract syntax tree is constructed from them.

## Type Checking

Type checking operates on the abstract syntax tree and is defined by the metamodel.
