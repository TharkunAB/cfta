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
symbolic names, type synonyms, and data families with an explanation at the
splice. Such types need a manual view where the existing APIs support them.
Views with records of measures also remain manual; this operation generates
the scalar views used by typing rules and single-measure invariants.

## Use and validation

Enable `TemplateHaskell` and `DeriveGeneric`. Put `$(deriveNode ''Expr)` after
the source datatype. The splice ends the declaration group, so subsequent
rules can use the generated constructors. A source change regenerates the
view in the same compilation.

Compare a generated arithmetic view with a manual view through the existing
typing and refinement APIs. Check bounded terms, counts, rank/unrank, records,
parameters, and newtypes. Compile unsupported declarations and name collisions
to check diagnostics. Run the repository PR gate under the memory cap.

## Authoring follow-ups

Keep this operation independent of quasiquoters. The typing-rule and explicit
LTA notations can use the generated view once their syntax is specified.
The shared TODO tracks separate investigations for EBNF, richer object-language
types, Lean interchange, file diagnostics, and complete authoring examples.
