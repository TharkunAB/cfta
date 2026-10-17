# Stored substitution row origins

Proof checkpoint: `a4b6e12d`. Source main: `c0cc8a05`. Local merge: `896b0a1c`.
The full-library contract remains in notes-proof-status-20261017.md.

## Established results

SourceCurrentStoredPlanEquivalence compares two independently covered
capture contexts in one coherent source heap. It permits different local
slots, repeated captures, and arbitrary nested binders. Equal name resolution
produces equivalent complete plans. build_execute relates the shared lexical
plan to its resolved stored substitution. recapture preserves the original
replacement environment exactly. Both equations hold at any current heap,
including pending outcomes and all cache effects. No current validity,
growth, or successful-return premise is required for that equality.

SourceCurrentSubstitutionRowExecution derives the ordered ChildTrace from
actual completed buildMany. Each child index retains its original occurrence
and exact prefix, call, and suffix heaps. rows_indexed follows literal
buildEdges and makeEdge. It retains the complete guard, symbol, child values,
and arity. node_indexed follows actual makeNode normalization. An output
index maps to an existential source/rebuilt occurrence index. The map need
not be unique or injective and need not preserve normalized row numbers.

SourceCurrentStoredSubstitutionCalls converts the entire shared encoded
trace to Calls of each child's own stored executor. It rewrites each actual
call at its own reached heap with recapture. It keeps the same replacement
environment and ordered prefix/suffix calls. The source coherence,
availability, and capture coverage can come from an earlier source heap.

SourceCurrentStoredSubstitutionOrigins proves NodeRows and UnionRows.
NodeRows retains the actual row-list build, normalized node pair, indexed
source row, row-list prefix, literal child Calls, exact edge pair, and
row-list suffix. Guards, symbols, and arity are exact. UnionRows retains the
actual ordered member Calls and final union pair. Its complete epsilon
Origin rows are exactly the rows of indexed actual member returns, at any
fixed view. Those returns are substituted values, not unchanged source
members.

node_complete and union_complete construct actual completion from initial
SemanticHeap, Covered [], source availability, and replacement availability.
They derive the final semantic heap, coverage, available result, and causal
History from the actual build. They split the exact closed-root identity
case from open reconstruction. No future completion or returned origin law
is an input. Arbitrary nested Mu children are included. The result stops
at the literal child executions; it does not claim their recursive source
row relation through retained Mu.

## Checked boundary and next proof

SourceCurrentStoredRebindBoundary.witness constructs a closed used outer Mu
whose raw inner Mu uses the outer name and ignores its own name. Its actual
ordinary probe retains that raw inner Mu. Actual stored self rebinding
compiles the open inner Mu with smart cleanup. Its result therefore differs
from the original ordinary probe. The proof derives source execution,
Facts, availability, closedness, the selected table payload, outer usesLocal
true, successful rebinding, and physical inequality. It assumes no future
success. This does not refute the earlier unused outer-Mu theorem.

The same constructed integration retains root symbol 0, full guard false,
arity two, and the first ordered child. Actual repaired unfolding of the
ordinary probe's unequal inner child returns the exact rebuilt child and
heap. This evidence supports a relation that permits epsilon exposure and
cleanup. It does not prove that general relation.

A possible next producer starts with Ready before, actual History empty
before, an actual selected Mu payload, usesLocal true, and an available
replacement. It would construct stored-body self substitution, then
ordinary-probe name substitution in the first call's returned heap, with
equal returned values and retained readiness/history. This is an unproved
candidate. It must derive payload availability and both fixed-support
freshness facts from the actual writer. Current probes must align with the
selected winner. Reconstruction fusion and the causal first-writer law are
still missing. History.retain gives no heap growth; use actual execution
growth for any replay argument. Do not assume a desired stored law, future
success, Cap, Prepared fragment, or global closure as a substitute.

Use the result to establish retained-Mu exposed row fields and ordered child
origins, then compose with the current native callback row receipt and
protected native edge histories. General recursive outer-node progress,
nonempty live walks, full mutual completion, convergence, frontend/error
adapters, concrete runtime effects, and public Haskell composition remain open.

## Validation and repair handoff

Full pinned Audit: 3089 jobs and 67978 dependency checks. Actual limits:
MemoryMax=MemoryHigh=4294967296 bytes, memory.swap.max=0. Peak: 367 MiB.
All five final source logs are empty. Canonical builds pass. The 27 public
declarations and six constructed checks form 33 signature/axiom pairs in
nine groups. Public groups print complete proof terms. Selected logs have
no diagnostics, omissions, or sorryAx. Only standard kernel axioms occur.
The preserved source already has one unused-input warning in canonical
and Audit replay logs; new source and selected probe logs are clean.

Evidence is in restart-evidence/20261017-substitution-row-origins/.
All earlier proof, counterexample, repair, and draft bytes are preserved.
No Haskell behavior patch or new production defect is added. The new
counterexample constrains the theorem statement. Root FINDINGS retains
merged field-pool repair b9219b9e and all earlier repair handoffs. Unchanged
Haskell source reuses the strict Nix build, 798 examples plus golden,
Fourmolu, and Cabal-gild validation.
