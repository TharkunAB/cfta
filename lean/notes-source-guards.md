# Complete guard control and sparse structural observations

`SourceGuards.lean` models every current source Guard constructor: Top,
Bottom, Same, Entails, Satisfies, Holds, Substitute, Not, And, and Or. It also
models every supporting actual-identity table operation in
`Refinement.Evaluate`: actual-path collection, ascending path-set order,
representative selection, conflicts, fresh declarations, ambiguity,
substitution resolution, simultaneous scope order, ambient assumptions, and
scoped solver bindings. Holds aliases repeated paths to their first formal.

The evaluator uses a polarity parameter for the source's pushed-negation
cases. Satisfies and Holds negate the requirement formula. Missing positions
remain distinct from failed entailment. An unresolved substitution returns
No, and its negation returns Yes. Formula syntax operations and the scoped
solver are explicit interfaces. This is a pure stable-query projection; it
does not claim equality of arbitrary IO traces or unstable solver behavior.

`SourceObservations.lean` implements source structural name substitution.
The first non-identity mapping for a formal wins. Annotation substitution
uses the same unique name map. Complete-term substitution changes labels and
keeps every constructor child. Sparse comparisons follow the source cases:
unequal roots are false, equal leaves are true, a leaf/inner mismatch is
false, and equal-root inner or Mixed observations remain unknown.

`sameShape_sound` proves that each decided sparse comparison agrees with the
complete renamed-tree comparison. It holds for every simultaneous scope and
every formula operation interface. This proof does not assume that equal
constructor labels identify complete inner terms. The public complete-term
and sparse evaluator entry points use their respective equality callbacks.

`SourceActuals.lean` proves that the finite fresh-name stream supplies every
requested declaration, contains no duplicate target names, and avoids all
observed and formula names. Allocation cannot truncate a conflict through
zip. Resolution requires both paths, preserves the literal symbol names
separately from solver identities, and carries ambiguity into the resolved
scope. `ambiguous_iff` gives the exact source collision witnesses.

`ambiguous_never_no` proves the source safeguard: an entailment query cannot
return No when its active scopes contain an uncertain actual identity. The
kernel checks include distinct inner results with the same root name, a
reserved-looking observed name that fresh allocation must avoid, repeated
uses of one actual path, and conversion of a solver No to Unknown.

Sparse evaluation is not generally verdict-equal to complete-term evaluation
for substitution guards. Complete comparison can identify two equal inner
subtrees, while sparse comparison cannot. The source then uses separate
fresh values and suppresses refutation when identity is uncertain. A full
pruning theorem for this case must transport entailment through fresh-name
renaming and identification of actual values. Those solver/query laws and
that transport remain open. The current theorems do not replace them with a
blanket assumption that sparse observations decide complete guards exactly.

The Formula interface still needs an explicit adapter to the repaired full
`FormulaSubstitution` implementation. Its name-only substitutions and
conjunction simplification have separate semantic foundations in Formula*
modules. The source's stronger symbol-sensitive signature must also connect
to this complete observation representation. Existing ObservationGraph
pruning theorems cover the declared refinement atom fragment.

Validation: `lake build MicroCFTA.SourceActuals` builds all three modules with
the pinned toolchain. There are no proof placeholders or new axioms.
