# Positive positions through an actual capped Head

Date: 2026-10-21 06:02 CEST.
Source: SourceCurrentCappedHeadPositivePosition.lean, 60 lines.
SHA-256: f34430290bf3cbf04cbbbf590779fd52c0bb6abd8e09f6d85735d33995e5dfb8.
The sole public theorem is head.

The actual Head.read constructor supplies the SAME completed row read and makeNode equation.
Public read_effects supplies its intermediate physical facts and resident rows.
Public makeNode_edges identifies the returned canonical surviving rows.
Their membership maps back to the same full raw read row.
Public node_ordinary excludes a returned union-positive branch.

For a root-row positive, the proof chooses that raw read row's actual list index.
It applies public CappedProjectionPositivePosition.root to Project.root and the SAME underlying Read.done fuel exposed.
For a child positive, it applies the corresponding public child observer.
The full row, child index and positive suffix remain exact.
The raw read index can differ from the normalized output index.
The reader is the original before heap, with reflexive Keeps and its original semantic/guard premises.

There is no private head_positive access, copied collector induction or Mu body-as-nodeEdges substitution.
The entry cap, SemanticReady, CostHeap, Available and GuardHeap Plain are genuine premises.
No closure, native History, future callback completion or desired origin is supplied.
The result preserves PositiveAt through a supplied successful Head.
It does not construct Head completion or prove global termination or original-program ancestry.

## Validation

Two actual owned Lean 4.34.1 commands ran.
Each had effective memory.max/high of 4 GiB, zero swap, a five-minute timeout and fresh usage above one percent.

- head-direct-1: personally observed terminal zero and exact zero-byte raw log.
- head-public-1: personally observed terminal zero; complete type, proof and axioms readback is 100,046 bytes.

The standalone verifier checks all eight printer options, no proof omissions, no private names in the public type and the standard three-axiom bound.
There were zero failed or warning checks, zero canonical jobs, one new public pair and zero constructed pairs.
No official source, old frozen evidence, Haskell, Audit, commit or publication was changed by this package.
