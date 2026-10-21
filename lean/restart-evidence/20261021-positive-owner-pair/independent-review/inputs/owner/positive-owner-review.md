# Positive owner pair

The sole public theorem is `SourceCurrentPositiveOwnerPair.same_child_pair`.
It is a pure geometry consumer. It makes no execution or termination claim.

The inputs are an actual congruence fixed point, a literal ordinary owner,
one member row with a nonplain guard, a child index, and a backwards
`PositiveAt` relation into that same row's literal child forest. The theorem
returns one class with two distinct path suffixes through the chosen index.
It requires no caller enumeration, function, common anchor, or count bound.

The private enumeration follows literal node children and union members.
It uses structural mass only to bound its internal recursion. Union choices
add no child index. The exact `PositiveAt` filter removes all extra candidate
paths. It also keeps Mu bodies and references opaque. `eraseDups` removes
path duplicates across rows, child occurrences, and union alternatives.
Completeness follows induction on `PositiveAt` with the existing strict
node-child and union-member mass bounds.

The selected nonplain row makes the empty path positive. Every backwards
witness lifts through the same selected row to a nonempty owner path.
If all classes dropped at the child, `child_separate` would make collisions
in this relation injective. The public relational cardinality theorem then
maps the distinct positive path list into that same list with its empty path
removed. The strict length decrease gives a contradiction. The common anchor
is a collision target inside this injectivity proof. It is not an input.

The source-only draft had 122 lines. The first strict attempt failed because
this import set has no `by_contra` tactic. The final source replaces its two
uses with `Classical.byContradiction` and `intro`. No public statement or
mathematical proof step changed. The final source has 124 lines.

Selected checks are `positive-owner-direct-2` and `positive-owner-public-1`.
The strict log is empty. The public log contains the full theorem type,
proof, and axiom report. All eight printer settings are explicit. The
`#check` type and `#print` type are identical after whitespace normalization.
The only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
All three actual Lean commands retain their immutable sources, raw logs,
receipts, fresh usage observations, and effective cgroup limits. There is one
retained elaboration failure, no warning, no canonical job, and no fixture.

An execution application must still derive the backwards relation from the
same literal selected row and the actual class family. This theorem does
not derive historical native support, causal history, class `Covers`, an
actual child dispatch, owner exclusion, renewal, or global completion.
