# Current library proof status and initial recursive reader bounds

This increment starts at published cb91c41e. Proof commits are c00bff2c,
9bba0158, and bd5c4fcc. Source main remains c0cc8a05, merged locally at
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
| Recursive row reads | Closed recursive collection and row exposure complete with pure initial computable fuel, exact returned heaps, resources, and stable replay. | Initial comparison and full selected Operand numeric forecasts. |
| Recursive intersection | Supported closed original operands construct stable semantic execution at a computable initial fuel ceiling. Full Mu, references, unions, swaps, resets, rows, and child traversal remain present. | General constrained callers and public runtime correspondence. |
| Native query programs | One initial numeric forecast constructs finite indexed query programs. Later calls use actual preceding results. Exact language, readiness, populated tables, captured origins, global validity, and numeric bounds follow on the same trace. | Actual caller lowering, complete interposed Operand numeric forecasts, adaptive control flow, and concrete capacity. |
| Selected Operand | Selected support constructs its actual projection and Merge and retains the complete generated-query frame. The mixed endpoint also derives its selected cap and retained Merge laws. | A numeric forecast for the complete Operand from initial forest and path data. |
| Mixed editor and class pass | Actual reads and the source class order retain stores and finite syntax depth. | General first Target and Force misses and complete editor and class execution. |
| Ordinary constrained reduction | Initial profiles construct a complete modeled pass with guarded language and store laws. | General recursive values, outer descent, and repeated reduction convergence. |
| Other components | Earlier equality, arithmetic, union-find, memo, generation, ranking, sampling, and restricted-driver proofs remain preserved. | Current adapters, remaining callers, and complete public pipelines. |

A passing build or a theorem count does not give a completion percentage.
These are explicit modeled workers and cache invariants. They do not yet
prove complete correspondence with compiled Haskell execution.

## Initial computable reader endpoint

The collector fuel is a pure function of initial node counter N, edge counter
E, causal stored payload mass B, and literal pending occurrence count k.
Define Q = max(max N E)(max B (k*B)). The fixed control function is
`g(q) = q + charge(q) + ceiling(q) + 1`.

The controlled descent bound F has these equations:

```text
F(0,q) = q
F(d+1,q) = iterate (x -> g(F(d,x))) (q+1) q
collectFuel(N,E,B,k) = F(B+1,Q)
readFuel(N,E,B) = F(B+1,g(initialControl(N,E,B,1)))
```

`HeightOrderControlled` proves the majorant. A higher-coordinate decrease
can refill lower coordinates above their initial values. A fixed initial
radix therefore does not suffice. The proof decomposes an actual path into
lower-dimensional blocks and higher-coordinate decreases. It derives both
its consumed length and final control bound. It does not assume a future
coordinate ceiling or path length.

`InternedValueMassBinderDepth` bounds full literal stored-plan depth by
causal payload mass. It includes complete Mu bodies and both constructor
probes. Initial B therefore fixes B+1 degree coordinates. Arbitrary cached
metadata is not used as that bound.

`SourceCurrentAllocatedReaderControl` models each actual pending-list
successor. Its Good facts retain semantic, coverage, depth, degree,
availability, and closure facts. Fits controls stored payloads, node and
edge counters, and pending structural weight. A fresh Mu successor derives
its own actual decoded unfold and allocation. Each actual successor retains
Good, Fits at g(q), and strict Mu-degree vector decrease. Visited Mu and union
skips and ordinary and empty values remain explicit.

`SourceCurrentAllocatedReaderConsumed` extracts a true Run and consumed
count from a successful collector. It reconstructs the exact ordered rows,
visited state, and returned heap at that count. It also proves identical
results at every larger fuel. This operational bridge needs no semantic
readiness premise or future resource certificate.

`SourceCurrentAllocatedReaderNumeric.collect_complete` combines these
results. Initial physical facts and Stored B construct success at collectFuel.
The existing qualitative termination proof only supplies a finite Run to
extract. The independent majorant then bounds that Run from its initial
state. The qualitative fuel does not occur in the numeric formula.

`SourceCurrentAllocatedRowReadNumeric.complete` constructs the complete
nodeEdges read at readFuel. It pays the preliminary direct Mu unfold before
any collector fallback. The fallback reads the original root in the actual
reached heap with a fresh visited list. It does not substitute the unfold
result for that root. The endpoint returns the same actual Projection Read,
Keeps, semantic readiness, stored mass, absolute node and edge bounds,
resident closed rows, and stable replay at every larger fuel.

The full-store bounds use readFuel itself as a conservative absolute ceiling.
Earlier successful-transfer schedules remain available where row length or
more detailed mass envelopes are needed. These logical bounds do not count
Haskell bytes, internal constructor instructions, solver work, or wall time.
The computed majorants can be very large. Tests keep them symbolic.

## Remaining work

1. Derive an initial computable comparison bound. Existing comparison and
   selection mass transfers still depend on explicit or existential successful
   comparison fuel. Their intermediate reads can allocate new cells. Control
   the unfinished Mu-degree vector, actual heap changes, pair universe, and
   ordered row, cover, and child stages from initial inputs. Read
   next-comparison-survey.md in the evidence directory.
2. Complete general memo-aware Merge Run and Call resource bounds. Include
   actual selection, ordered rows and columns, and first-winner rereads.
   Then forecast a complete selected Operand from initial counters, causal
   mass, forest occurrence count, and path length. Preserve selected support
   that permits unrelated open ordinary roots. Availability alone does not
   bound duplicate occurrences in a supplied list.
3. Compose Target in source order: head Operand, recursive tail, checked
   query. Derive reached range assumptions from the initial schedule.
   Construct a Force miss and captured slot law. Retain exact state identity
   on a repeated hit. A native-query sequence does not cover interposed work.
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

The top-level contract and full library scope remain unchanged. Preserve
all older proofs, counterexamples, repairs, marked drafts, the optimized
interned core, and the older constructor and equality work.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2905 jobs and 64482 dependency checks.
All six production strict logs are empty. All 71 imported full signature
and axiom pairs pass in nine groups: 55 distinct public declarations, seven
independent repeat checks, and nine constructive integrations. Only propext,
Classical.choice, and Quot.sound occur.

The integrations construct controlled lower-coordinate refills, actual fresh
Mu and union steps, consumed exact and warm replays, a nested Mu/union with
duplicate pending occurrences, a productive raw Mu, and a real union that
contains that Mu. Numeric reads derive their own initial causal mass. They
return the exact full heap on warm replay. No future successful execution
or returned resource certificate is supplied.

Six proof component manifests verify 136 immutable entries. The separate
next-comparison survey adds 26 entries and 48 exact excerpts over 19
production sources. It records a proposed next proof sequence. Aggregate
validation checks seven manifests with 162 entries. Read
checkpoint-validation.json for all component totals
and exact source and log hashes. All earlier failed attempts retain their
source snapshots and raw logs.

Preservation retains 13551 starting files, 2898 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, both stashes, and three
other worktrees. All 81 frozen module manifests retain their 662 entries.
The complete public library goal stays active.

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
