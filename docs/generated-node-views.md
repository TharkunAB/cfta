# Generated node views

Typing rules and refinement invariants use a node view of the source datatype.
The view repeats every constructor and field. A hand-written view can become
stale when the source datatype changes. Generate the repeated structure from
that datatype, then use the existing `NodeView` methods and shape checks.

## Scope

Add `deriveNode :: Name -> Q [Dec]` in `Data.CFTA.TH` in a new `cfta-th` package.
Only this package depends on Template Haskell. The core and generator packages
keep their current dependencies.

For `data Expr = Lit Int | Add Expr Expr`, generate `ExprNode e` with
`LitNode e` and `AddNode e e`, in that order. Derive `Generic` and declare the
`NodeView ExprNode` instance. The user supplies `HasFTA Expr` as before.
The splice replaces the manual node view; it does not change typing rules,
refinement semantics, counting, or rank order.

Append `Node` to type and constructor names. Check for names already in scope.
Keep constructor order and field count. Make every field a plain `e`, including
fields of a record and fields whose types contain source type parameters.
Do not copy record selectors, strictness, or source type parameters to the view.
The result has one parameter: the type of a child observation or premise.

Accept ordinary `data` and `newtype` declarations with named constructors.
Reject datatype contexts, existential or constrained constructors, GADTs,
symbolic names, names ending in `#`, type synonyms, and data families with an
explanation at the splice. Such types need a manual view where the existing
APIs support them.
Views with records of measures also remain manual; this operation generates
the scalar views used by typing rules and single-measure invariants.

## Use

Enable `TemplateHaskell` and `DeriveGeneric`. Put `$(deriveNode ''Expr)` after
the source datatype. The splice ends the declaration group, so subsequent
rules can use the generated constructors. A source change regenerates the
view in the same compilation. An empty datatype also needs
`EmptyDataDeriving` for the generated instance.

## Validation

A standalone check compares generated and manual views through the existing
APIs. All 38 arithmetic terms have the same ranks and decode correctly.
Scalar refinement counts and rank order also agree. Two processes produce
the same results. Records, source parameters, named infix constructors,
newtypes, and empty datatypes have the expected shapes.

Nine invalid declarations produce the expected diagnostics. The complete
README module compiles with strict warnings. Editing a source datatype and
recompiling the same module adds the new constructor to its generated view.
A fresh `-O0 -Werror` build and all six existing suites pass. Formatting and
lint pass. Validation runs serially through heavy-management with a 12 GiB
process cap and a 4 GiB test RTS limit.

## Authoring follow-ups

Keep this operation independent of quasiquoters. The typing-rule and explicit
LTA notations can use the generated view once their syntax is specified.
The shared TODO tracks separate investigations for EBNF, richer object-language
types, Lean interchange, file diagnostics, and complete authoring examples.
