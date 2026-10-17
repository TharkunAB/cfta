# Current library proof status and selected Operand resources

This increment starts at published b0bd69c6. Proof commits are 8440539c and
3152aaf8. Source main remains c0cc8a05,
merged locally at 896b0a1c. The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove this contract:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of target contracts. There is no completed universal public
library theorem. Specify the intended behavior first. Then prove that the
current Haskell implementation has that behavior. Support must use initial
input and resource conditions. It must not assume successful future calls or
the required result. Documented errors and validation order are observable.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverse laws, transformation
language relations, generation coverage, and sampling laws. Language equality,
inclusion, and representative restriction have different contracts. Terms,
accepting runs, and generator members have different definitions.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. | Current host and solver adapters and full public composition. |
| Interned construction | Modeled repaired construction, including nested Mu and unions. Causal physical stores bound full returned and stored payload mass. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive intersection | Supported closed original operands construct stable semantic execution at a computable initial fuel ceiling. Full Mu, references, unions, swaps, resets, rows, and child traversal remain present. | General constrained callers and public runtime correspondence. |
| Native query programs | One initial numeric forecast constructs finite indexed query programs. Later calls use actual preceding results. Exact language, readiness, populated tables, captured origins, global validity, and numeric bounds follow on the same trace. | Actual caller lowering, interposed Operand resources, adaptive control flow, and concrete capacity. |
| Selected Operand | Selected support constructs its actual projection and Merge and retains the complete generated-query frame. The mixed endpoint also derives its selected cap and retained Merge laws. | A numeric forecast for the complete Operand from initial forest and path data. |
| Mixed editor and class pass | Actual reads and the source class order retain stores and finite syntax depth. | General first Target and Force misses and complete editor and class execution. |
| Ordinary constrained reduction | Initial profiles construct a complete modeled pass with guarded language and store laws. | General recursive values, outer descent, and repeated reduction convergence. |
| Other components | Earlier equality, arithmetic, union-find, memo, generation, ranking, sampling, and restricted-driver proofs remain preserved. | Current adapters, remaining callers, and complete public pipelines. |

A passing build or a theorem count does not give a completion percentage.
These are explicit modeled workers and cache invariants. They do not yet
prove complete correspondence with compiled Haskell execution.

## Selected Operand frame

SourceCurrentConstrainedCapOperandFrame.advance retains the same inventory,
its admission, semantic and guard context, completed joint laws, and captured
origins through actual heap growth and unchanged native cells.

The actual projection derives its guard heap. Actual Merge retains that heap
through comparisons and constructors. The resulting full Frame refers to the
literal returned Checked state. No all-root cap is needed for Frame retention.
Selected closure permits unrelated open ordinary roots.

The complete endpoint constructs its own Operand graph and existing full
receipt from initial support. The mixed endpoint derives its result cap and
the retained Merge laws at the same return. That endpoint uses the earlier
all-root cap interface. It does not cover every class accepted by the broader
source gate.

One integration constructs three consecutive Operands and every intermediate
Frame. A second retains an unrelated open reference and permits unequal path
lengths. A third constructs a generated query from initial room and its
numeric profile. It then passes the literal returned result to an actual
Operand beside an open sibling. That Operand retains the query's exact native
tables, full Frame, cap, Merge laws, and global validity. No future Frame or
completed Operand graph is supplied.

## Numeric reader and comparison boundary

Recursive row exposure already has a termination proof based on a dynamic
Mu-degree vector. A lower-degree Mu can allocate more records. The original
node count alone does not supply a numeric bound on the reader fuel.

The new reader component derives causal payload and supply bounds for actual
stored substitution and unfolding. It includes the complete stored Mu body,
both constructor probes, unions, references, and physical warm winners.
Fuel-indexed collection and successful row reads then derive their own mass,
counter, resident-row, and row-length bounds. They use the existing massAfter
and credit schedules.

The numeric comparison and selection components derive local bounds from
the initial causal store and explicit comparison fuel. They retain actual
repaired recursive row exposure. They do not accept a future per-comparison
resource law. A successful-transfer theorem with supplied comparison fuel
does not derive the successful fuel from initial source data.

The causal Merge winner component bounds the actual returned entry from
physical Stored and the current causal mass bound. A smaller losing candidate
does not bound an older larger winner. Its call transfer theorem uses the
produced final invariants. It is not an initial-only Merge completion producer.
The integration constructs the earlier winner, a distinct smaller candidate,
the keep-first reread, and the subsequent unchanged warm call. It does not
assert that the enclosing literal Merge body performs that nested publication.

## Remaining work

1. Derive numeric recursive reader and comparison fuel from initial inputs.
   Convert the Mu-degree termination argument to an initial computable bound.
   Then complete general memo-aware Merge Run and Call resource bounds.
   Include actual selection, ordered rows and columns, and first-winner rereads.
2. Forecast a complete selected Operand from initial counters, causal mass,
   forest occurrence count, and path length. Availability does not bound the
   number of duplicate occurrences in a supplied forest list. Retain the
   selected source domain instead of requiring unrelated roots to be closed.
3. Compose Target in the actual order: head Operand, recursive tail, checked
   query. Derive its reached range assumptions from the initial schedule.
   Construct a Force miss and its captured slot law, then retain exact state
   identity on a repeated hit. A native-query sequence alone does not do this.
4. Complete mixed Edit and ClassPass and initial active and stored outer
   descent. Cover arbitrary constrained Mu bodies and the full source gate.
   Semantic narrowing alone does not prove immutable output-height bounds.
5. Prove repeated reduction convergence and remaining recursive callers.
   One complete pass does not prove convergence.
6. Complete current typing, refinement, and drawn-field adapters, symbolic
   measures, errors, validation order, and generator rank order. Complete
   solver, runtime, IO, randomness, capacity, and user-code adapters.
7. Compose the complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines.

Logical payload mass is not bytes. A yielded Work or optionalBinder counts
once. Its internal constructor work and solver work need separate measures.
Conservative numeric ceilings do not give practical runtime or memory bounds.
Preserve all earlier proofs, counterexamples, repairs, and marked drafts,
the optimized interned core, and the older constructor and equality work.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2899 jobs and 64377 dependency checks.
All five production strict logs are empty. All 49 imported complete signature
and axiom pairs pass in nine groups. These cover all 35 distinct public
declarations, five independent repeat checks, and nine constructive
integrations. Only propext, Classical.choice, and Quot.sound occur.
Five proof component manifests verify 147 entries. The next-reader survey
adds 22 entries and 75 exact headers over 18 immutable production sources.
Aggregate validation checks six manifests with 169 entries.
Read checkpoint-validation.json for exact source and log hashes.
All failed attempts and their raw source snapshots remain preserved.

Preservation retains 13393 starting files, 2893 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, both stashes, and three
other worktrees. All 80 frozen module manifests retain their 656 entries.
Read next-initial-reader-resources.md and next-reader-survey.md in the evidence
directory. The complete public library goal stays active.

## Haskell handoff

No Haskell source change or new behavior defect occurs in this increment.
Root FINDINGS keeps the repair registry first. Repair b9219b9e is merged by
PR 65 in c0cc8a05. The unchanged Chain reproducer now returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds still treats supplied
pools as opaque. The repair rejects the invalid derivation configuration.
The historical failure and its original logs remain preserved.

Reuse the unchanged strict Nix build, 798 examples plus golden, Fourmolu,
and Cabal-gild evidence in 20261016-drawn-fields-local-worker. Record each
later Haskell fix in root FINDINGS with failure, reproducer, affected files,
commit, checks, and upstream status. Current frontend adapters remain open.
