# Admitted ordered native child traversal

## Current result

Child completion: `a8593e70a465299b3f1d2f6bda1320b9b07005f9`.
Traversal completion: `06fc7521a9d83a0d7a053c5f6496f02fc1e8d510`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

`SourcePruningEnumerationTraversalCompletion.complete` derives sufficient
common execution bounds for the existing ordered child worker.
The worker either completes all children or stops at its first valid
raw-empty rejection. Both outcomes retain the actual result cache.
This derives progress from admitted inputs. It does not assume a successful
trace or a successful future callback.

## Admission

The initial caller satisfies `Context`. The cache satisfies `Safe`, native
pending-value realization, a root map, canonical waiting counts and all-slot
native expandable flags. Each supplied child is available in the current
native heap and closed. Each child bucket is bounded by the initial counter
and satisfies `InputsPending`.

Numeric admission remains an explicit premise at the fixed width.
`CachedTerminalAdapter.Ranges` names the existing terminal request condition.
It is definitionally equal to the former inline premise.
The existing terminal completion proof body and all its outputs stay intact.
`ChildCompletion.Ranges` requires that condition only for a nonempty child
with a nonempty terminal partition.

`TraversalCompletion.Ranges` applies the head condition at the current state.
It requests suffix numeric admission only after an actual successful
singleton child call with a cache. This implication quantifies execution
bounds and the reached caller, cache and query map. It assumes no future
completion or cache correctness. Initial state bounds alone do not derive
this condition. An initial-only numeric admission theorem remains open.

## Child completion

Empty rejects immediately and retains the input cache.
A nonterminal bucket uses the existing cached shallow-child producer.
Its raw action supplies safety, enumerated-value origin and old-root
protection. The known nonterminal arm does not inspect representative fuel,
native fuel or `p/h`. A direct equality lifts the existing index-fuel result
to all those parameters without a repeated native query.

A terminal bucket uses the existing terminal completion producer.
The actual partition supplies bounded and pending terminal inputs and
bounded descendant inputs. The producer retains the merged root function,
actual post-write cache, counts, flags and caller effects.
Its output is either raw `[]` or one successful row at that cache's core.
The theorem retains `Safe` only for the successful singleton.
A rejected terminal cache need not satisfy `Safe`.

## Ordered induction

The traversal enters the tail only after a singleton success.
`Post.context` supplies the reached caller invariants.
Native heap preservation supplies availability of every remaining child.
Closedness belongs to the unchanged child value.
Counter monotonicity preserves all remaining bucket bounds.
Enumerated-value origin and old enumerated-root protection preserve pending
inputs for every remaining bucket. No parent-specific avoidance assumption
is used to establish this pending-input transport.

Representative, native and index-fuel bounds combine by addition.
The `p/h` bounds combine by maximum. All larger admitted bounds give the
same result and endpoints. The query map and actual cache pass to the next
child. The outer read state and intermediate waiting table do not replace
that cache. Fragment order and duplicate occurrences stay unchanged.

Completion retains `Safe` at the final cache.
Valid rejection retains storage, pending-value realization, roots, waiting
counts, expandable flags and caller `Post`. It does not retain unconditional
`Safe`. Rejection stops the suffix. No fault, malformed result or missing
cache is introduced under these admission premises.

Both outcomes retain counter monotonicity and fragment allocation bounds.
They retain enumerated-value origin and protect all old enumerated slots.
The separate general protection clause covers any initially allocated root
whose class every input bucket avoids. This includes pending roots.
Callers must prove allocation, rootness and bucket avoidance for the
captured parent slot. `InputsPending` does not prove these facts for a
pending slot. The final-write obligation therefore remains conditional.

`retained_inputs` transports any separately supplied parent bucket that
satisfies initial `InputsPending`. It uses the exported origin and old
enumerated-root protection. It also applies to a valid rejection cache.
It needs no unconditional safety claim for that cache.

## Verification

All three proof modules pass Lean 4.34.1 with all linters and warnings as errors.
Seven strict attempts are retained. Terminal admission passes immediately.
Child attempt 1 exposes a partition-filter expression and a missing opened
namespace. Attempt 2 exposes unused section instances. Attempt 3 passes.
Traversal attempt 1 exposes dependent match equality. Attempt 2 passes.
Attempt 3 adds conditional protection of arbitrary allocated roots and passes.
No linter or production proof-resource limit is disabled or increased.

Installed builds pass. Complete public readback covers seven declarations.
Its full log has 85439 bytes and SHA-256
`86af77952af3df7a745083093132a683faf2dda4374d99a6aa411d3ba003c1c8`.
All axiom sets are subsets of `propext`, `Classical.choice` and `Quot.sound`.
The aggregate Audit passes with 3739 jobs and 76623 theorem dependencies.
The older unused `inputs` warning remains unchanged.
Checks run serially under 4 GiB heavy-management caps with no swap.
Complete attempted sources, raw logs, reports and peak records remain in
`restart-evidence/20261025-admitted-child-traversal`.
Source review finds no semantic defect or hidden future-success premise.

No Haskell source or runtime worker body changes in this checkpoint.
The optimized interned core, historical repairs, counterexamples and older
constructor/equality work remain. H6's source is unchanged.
No runtime test is repeated for these proof-only changes.

## Next work and scope

Connect actual selected-edge own-class allocation to the admitted traversal.
The source inputs combine inherited descents with fresh own-class descents.
Derive their availability, closedness, bounds and `InputsPending` from the
existing selected-edge and suspension receipts.
Retain the conditional numeric ranges instead of assuming future success.
Then record the edge residual only after every child succeeds.
Each alternative must begin from the same captured parent input state.
Connect finalization to the original captured raw slot.
Do not replace that slot with the terminal merge winner.

H6 remains the strongest end-to-end result for covered closed construction,
valid initial cache/history, prescribed finite rounds, derived sufficient
fuels and one mathematical width, with exact finite-tree language preservation.
This checkpoint does not prove the whole typing/pruning pipeline, arbitrary
mixed calls, concrete solver correspondence, extraction, physical map and
machine-integer correspondence, practical resource bounds or convergence.
