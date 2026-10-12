# Resolved scopes and renamed actual assumptions

`SourceResolvedTables.lean` carries the constructed source table renaming
through substitution resolution. The avoid-list proof fixes every original
observed name. `resolve_tables` then gives the exact rebuilt resolved record.
It changes the logical replacement value and fresh declaration. It retains
the formal name, literal symbol replacement, declared sort name, and identity
flag. The actual-assumption field is rebuilt from the original actual
refinement and the renamed logical value.

`resolveMany_aligned` proves ordered scope correspondence, including missing
actual or formal positions. Both traversals fail at the same resolution
boundary. Successful scopes retain the same length and order through their
pointwise list relation. The list relation explicitly excludes a direct
formula-syntax equality claim for actual assumptions.

`SourceActualAssumptions.lean` proves that missing semantic field separately.
`resolve_tables_assumption` follows actual successful source resolution on
both sides. Under agreement on the original refinement's free values and
equality of the corresponding logical actual values, the two resolved
actual assumptions have the same full formula meaning. The proof uses the
repaired capture-avoiding substitution semantics. It therefore covers
quantifiers and function applications even when bound-name spellings differ.

The remaining whole-query composition must derive those environment
agreements uniformly through every nested scope and contract alias. The
source free-name bounds and sorted declaration-domain transport remain
explicit. These local theorems do not replace those obligations with a
postcondition on the complete guard evaluator.

Validation: `lake build MicroCFTA.SourceActualAssumptions` builds both modules
with the pinned toolchain. There are no proof placeholders or new axioms.
