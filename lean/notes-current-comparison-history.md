# Current library proof status and initial comparison and selection bounds

This increment starts at published b7b01355. Proof commits are d81f7b8e,
27b4031f, and 46485ba9. Source main remains c0cc8a05, merged locally at
896b0a1c. The complete public Haskell theorem remains open.

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
| Recursive row reads | Closed recursive collection and row exposure complete with pure initial computable fuel, exact returned heaps, resources, and stable replay. | Full selected Operand numeric forecasts and public runtime correspondence. |
| Comparison and selection | Actual repaired workers construct success from initial counters and causal mass. Exact history, full heap bounds, ordered failed covers, and stable replay follow. | General memo-aware Merge work and selection budgets and independent language-law composition. |
| Recursive intersection | Supported closed original operands construct stable semantic execution at a computable initial fuel ceiling. Full Mu, references, unions, swaps, resets, rows, and child traversal remain present. | General constrained callers and public runtime correspondence. |
| Native query programs | One initial numeric forecast constructs finite indexed query programs. Later calls use actual preceding results. Exact language, readiness, populated tables, captured origins, global validity, and numeric bounds follow on the same trace. | Actual caller lowering, complete interposed Operand numeric forecasts, adaptive control flow, and concrete capacity. |
| Selected Operand | Selected support constructs its actual projection and Merge and retains the complete generated-query frame. The mixed endpoint also derives its selected cap and retained Merge laws. | A numeric forecast for the complete Operand from initial forest and path data. |
| Mixed editor and class pass | Actual reads and the source class order retain stores and finite syntax depth. | General first Target and Force misses and complete editor and class execution. |
| Ordinary constrained reduction | Initial profiles construct a complete modeled pass with guarded language and store laws. | General recursive values, outer descent, and repeated reduction convergence. |
| Other components | Earlier equality, arithmetic, union-find, memo, generation, ranking, sampling, and restricted-driver proofs remain preserved. | Current adapters, remaining callers, and complete public pipelines. |

A passing build or a theorem count does not give a completion percentage.
These are explicit modeled workers and cache invariants. They do not yet
prove complete correspondence with compiled Haskell execution.

## Initial numeric comparison and selection

Let N and E be the initial node and edge counters. Let B bound complete
stored payload mass in that initial heap. The earlier controlled majorant F
uses the fixed monotone strict control function g. The new definitions are:

```text
Q = F(B, max(max N E) B)
R = readFuel(Q,Q,Q)
comparisonFuel(N,E,B) = 1 + Q*Q + R
```

These are pure computable definitions. They contain no successful future
fuel, final counter bound, returned state, or completion certificate.
The unfinished-record predicate is proof-only. It does not occur in the
computed numeric formula.

`SourceCurrentAllocatedUnfoldHistory` records exact successful closed
unfold events at their own starting heaps. Each heap-changing event strictly
decreases the unfinished Mu-degree vector. Exact heap replays retain the
same numeric control. The proof removes these stutters before applying the
controlled-path theorem. Initial causal mass fixes the degree dimension.
Every actual history prefix therefore derives semantic facts and an absolute
Q bound for stored payloads and both counters. The bound is independent of
the enclosing comparison fuel and the number of allocation-free replays.

`SourceCurrentAllocatedReaderHistory` extracts that exact history from each
actual consumed collector run. The nodeEdges history also records the direct
Mu unfold before fallback. The fallback uses the original root in the
literal reached heap. Canonicalization changes rows but does not alter the
recorded heap. The comparison read wrapper retains the same history.

`SourceCurrentAllocatedRowReadUniform` proves one sufficient readFuel(Q,Q,Q)
for every reached heap with Stored Q and both counters at most Q. Successful
earlier reads align by uniqueness of their complete returned rows and heap.
Closed nonempty available operands have identities below Q. The finite
ordered identity-pair universe has at most Q*Q members.

`SourceMergedComparisonHistory` retains physical Budget and exact histories
through every demanded child, candidate cover, narrow row, and comparison.
False child and cover answers retain their actual effects. The final
comparison discharges recursive callback tracking by its own fuel induction.

`SourceMergedComparisonReplayStages` replays these literal ordered stages
at the same full intermediate heaps. Its local callback and reader replay
premises are discharged by the complete comparison proof. They are not
premises of the final initial-input endpoint.

`SourceMergedComparisonNumeric.check_replay` inducts on the old actual
successful comparison. Every recursive path adds a fresh ancestor pair.
Its remaining-pair allowance strictly decreases inside the fixed Q universe.
The initial uniform reader bound pays every demanded row read. Sibling scans
do not consume recursive depth fuel. The proof replays the same result at
any sufficient allowance, even when it is smaller than the old witness fuel.

`check_complete` constructs its own qualitative successful witness internally.
It then replays that exact execution at comparisonFuel(N,E,B). The witness
fuel does not occur in the formula. The endpoint returns its exact Boolean,
full heap, physical Effect, absolute Fits Q, the earlier comparison resource
envelope at the computed fuel, and stable replay at every larger fuel.
It follows literal ancestor-hit behavior for arbitrary supplied above lists.
It does not add a language soundness law for arbitrary ancestor assumptions.
Existing independent language contracts retain their own conditions.

`SourceMergedSelectionNumeric` composes histories through anyAccepts,
retain, and select. The captured filtered recursive family stays fixed.
Failed comparisons retain their reached heaps before the next candidate.
Recursive members are retained directly. Duplicate removal has no heap effect.
One comparisonFuel from the original heap supports the complete finite scan.
The literal input length enters the outer selection resource envelope.
`select_complete` constructs its own exact success, Effect, Fits Q, initial
resource envelope, and stable larger-fuel replay. No future callback or
resource law is supplied.

The initial closed available input domain is unchanged. No prepared-body,
noMu, or ordinary-only condition is introduced. These endpoints do not require
unrelated roots of an enclosing forest to be closed. Actual selected-path
composition retains its existing source domain.

## Remaining work

1. Derive initial work and selection budgets for general memo-aware Merge.
   Bound the actual Code interpreter, constructor jobs, recursive requests,
   selected columns, and first-winner rereads. Include warm stored winners
   that differ from a smaller new candidate. Existing finite completion and
   causal winner mass do not yet provide a global initial worker forecast.
   Read next-merge-survey.md for exact source anchors and
   next-initial-merge-resources.md for the proposed full endpoint. Both are
   in the evidence directory.
2. Forecast complete selected Operand work from initial counters, causal mass,
   forest occurrence count, and path length. Compose the actual projection and
   Merge ordering. Preserve selected support that permits unrelated open
   ordinary roots. Availability alone does not bound duplicate list occurrences.
3. Compose Target in source order: head Operand, recursive tail, checked query.
   Derive reached range assumptions from the initial schedule. Construct Force
   misses and captured slot laws, then exact repeated-hit state identity.
4. Complete mixed Edit and ClassPass and initial active and stored outer
   descent. Cover arbitrary constrained Mu bodies and the full source gate.
   Separate broader source gates from all-root cap assumptions. Semantic
   narrowing alone does not prove immutable output-height bounds.
5. Prove repeated reduction convergence and remaining recursive callers.
   One complete pass does not prove convergence.
6. Complete current typing, refinement, and drawn-field adapters, symbolic
   measures, errors, validation order, and generator rank order. Complete
   solver, runtime, IO, randomness, capacity, and user-code adapters.
7. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines.

Logical payload mass is not Haskell bytes. Comparison fuel bounds recursive
depth and local reader fuel. It does not count total sibling instructions.
Internal constructor and solver work need separate measures. The numerical
majorants can be very large. No practical runtime estimate is claimed.
The complete public library target and full supported source scope stay open.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2912 jobs and 64550 dependency checks.
All seven production strict logs are empty. Imported validation checks all
49 public declarations and 13 constructive integration declarations in 14
groups. All 62 complete signature and axiom pairs pass. Only propext,
Classical.choice, and Quot.sound occur. Seven proof component manifests
verify 159 immutable entries. The next-Merge survey adds 25 entries and
48 exact declaration excerpts over 20 production sources. Aggregate
validation checks eight manifests with 184 entries. Read
checkpoint-validation.json for all totals and hashes.
Failed proof sources, raw output, and the explicitly unchecked draft remain
preserved.

The integrations prove actual fresh Mu allocation, arbitrary warm stutters
under the same original heap ceiling, exact reader histories, uniform row
reads, and ordered replay after failed covers. The computed comparison test
builds a closed ordinary root with real Mu and union operands. It derives
its own initial mass and computed successful comparison. It proves the
actual false answer increases node supply and then replays at the exact
first returned heap. A synthetic forest with an unrelated open reference
proves selected closure at its two chosen positions and disproves whole-list
closure. This part tests the domain predicate. It does not execute a complete
projection or Operand through that forest.

The selection tests construct their own initial computed execution. Both
constructor counters increase. Warm selection reuses the same initial
origin, mass, and comparison fuel and returns the identical full heap.
The computed ceilings remain symbolic in all these tests.

Preservation retains 13694 starting files, 2904 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, both stashes, and three
other worktrees. All 82 frozen module manifests retain their 669 entries.
Preserve all earlier proofs, counterexamples, repairs, marked drafts,
the optimized interned core, and older constructor and equality work.
The whole library goal stays active.

## Haskell handoff

No Haskell source change or new behavior defect occurs in this increment.
Root FINDINGS keeps the repair registry first. Repair b9219b9e is merged by
PR 65 in c0cc8a05. The unchanged Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains its opaque
pool behavior. Derivation validation rejects the direct recursive field pool.
The historical failure and its original logs remain preserved.

Reuse the unchanged strict Nix build, 798 examples plus golden, Fourmolu,
and Cabal-gild evidence in 20261016-drawn-fields-local-worker. Record each
later Haskell fix in root FINDINGS with failure, reproducer, affected files,
commit, checks, and upstream status. Current frontend adapters remain open.
