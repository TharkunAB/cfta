# Ordered native child traversal

## Current result

Core agreement: `48c9d2f325c36225e9a2d9ef589636fd22b55af5`.
Traversal: `14c03485bd007c318da0093f2d4b4ed7593a0a6f`.
Main remains `9d4e4d584aa7a681f075790e98466afe7531838a`.
The goal stays ACTIVE.

`SourcePruningEnumerationChildTraversal.run` calls the dispatcher once per
child. It advances only after one successful raw row and a cache candidate.
It passes the reached caller, saved queries and actual post-write cache to
the next child. It preserves source order and duplicates. It does not use
the outer read state or intermediate waiting table as the next input.

`Result.complete` retains the ordered fragments and final caller, queries
and cache. `Result.stopped` retains the completed prefix, exact stopping
observation and optional candidate. Faults, outer `none`, rejection, malformed
raw results and missing candidates remain distinct inside that receipt.
A raw singleton with no candidate is the stopping call. Its fragment stays
inside the observation. The completed prefix contains only preceding steps
with caches. A rejected terminal call can still retain its after-write cache.
The stopping candidate need not equal the cache before that call.

## Core agreement

`CachedPrepare.erase_some` proves that successful cached preparation erases
to the original shallow-child action. It covers Empty rejection, ordinary
children and supported recursive boundaries. It needs no storage, native
availability, coherence, path termination or admission premise.

Incoming adaptation frames the actual returned core. Its singleton helpers
export that equality. Terminal propagation preserves the incoming row core.
`ChildDispatch.singleton_core` combines both routes at every fixed bound.
A successful singleton and a returned cache therefore have the same core.
The traversal uses that returned cache directly. It performs no runtime
state comparison and does not repair a cache with an old waiting table.
This equality does not prove that arbitrary candidate indexes are correct.

`ChildDispatch.Observation` is now a public type abbreviation. Its type is
definitionally equal to the former local notation. All existing runtime
function bodies remain unchanged. Existing completion producers, admission
premises and proof resource limits remain unchanged.

## Trace proofs

`Trace` records the actual dispatcher call for each child. The raw row core
is the next cache core. It retains every intermediate caller and query map.
`trace_complete` derives the worker result from this trace. `complete_trace`
derives the same trace from any completed worker result.

`uncached` proves that a missing candidate stops without running the tail.
`stopped_trace` derives an input-list decomposition, an actual trace for the
completed prefix, and the exact next child call that produced the retained
observation and candidate. These results hold at fixed execution bounds.
They assume the stated runtime result. They do not assume successful future
callbacks. They do not construct completion from genuine initial admission.

## Verification

All strict checks use Lean 4.34.1, all linters and warnings as errors.
Heavy checks run serially with 4 GiB caps and no swap. The cap probe records
both effective memory limits as 4294967296 and the swap limit as zero.
All final strict logs are empty.

Incoming attempt 1 checks the adaptation helper. Attempt 2 adds and checks
the actual observation helper. Preparation attempt 1 fails on a theorem
qualification; attempt 2 passes. Terminal attempt 1 fails on constructor
patterns and an unknown simplification lemma. Attempt 2 fails the constructor
name linter. Attempt 3 passes. Dispatch passes its first strict check.

Traversal attempt 1 fails on the reserved identifier `prefix` and missing
constructor documentation. Attempt 2 exposes theorem-name shadowing.
Attempt 3 checks the completed-trace result. Attempt 4 adds stopped traces
and exposes missing pattern-match equality reasoning in `uncached`.
Attempt 5 supplies that reasoning and passes. All complete strict inputs,
including rejected inputs, and raw logs remain in the evidence.

The installed build passes with 1330 jobs. Public readback covers thirteen
declarations. Its complete log has 300 lines and 19762 bytes, with no display
omissions. Every axiom set is a subset of `propext`, `Classical.choice` and
`Quot.sound`. `Observation` and `Result` use no axioms.
The aggregate Audit passes with 3736 jobs and checks 76594 theorem axiom
dependencies. This count includes generated declarations. The older unused
`inputs` warning remains unchanged. Source review finds no endpoint defect.
Evidence: `lean/restart-evidence/20261025-child-traversal`.

## Next target and limits

Derive complete traversal from genuine initial inputs and current conditional
numeric admission. Compose the existing per-child completion producers.
Use `Post.context` and heap-preservation receipts to transport the remaining
children's availability. Thread each new root map, waiting table and cache.
Use `ChildEffects` to preserve safety, old roots and pending parent inputs.
Actual buckets combine inherited and fresh-own descents; handle that append.
Do not replace this work with a premise that every future callback succeeds.

Connect own-class allocation and the selected edge's child buckets to this
worker. Record the residual only after every child completes. Each alternative
must start from the same parent state. Then connect the final write to the
original captured raw slot, which can differ from a terminal winner.
Initial-only numeric admission across growing heaps remains open.

H6 remains `SourceCurrentColdFiniteWarmCalls.constructed_node_calls`.
Covered closed construction from a valid initial constraint cache and original
allocation history supports any prescribed finite number of modeled warm
node calls with the same empty inherited payload, at derived sufficient
finite fuels and one mathematical width. The final available value has
exactly the original finite-tree language under formal guard semantics.
Full native enumeration completion, whole typing/pruning, concrete solvers,
extraction, physical maps and machine integers, practical resources,
convergence and full Haskell correspondence remain open. H6 is unchanged.

No Haskell source changes at this checkpoint. Root `FINDINGS.md` retains the
six merged repair entries and parallel-completion follow-ups before proof
status. Performance matrices remain outside the formalization scope.
