# Completed native intersection and guarded kernel correspondence

Proof checkpoint: `e9ade493`. Upstream: `f59c198d`, 2026-10-14.
Source: `Interned/Operations.hs:intersectOpen`, `intersectOpenEdge`, and
`Interned/FlatMemo.hs:lookupOrInsert`, `insert`, and `write`.

## Derived physical source safety

`SourceRecursiveIntersectionCodeSafety.Safe` retains actual effect caches,
complete physical/domain facts, and available original recursive inputs.
Continuations accept every valid available returned record after source
growth. `safe_bind` and `safe_walk` compose these facts with exact ordered
effects. Actual constructor and optional-binder verification supply the
primitive safety facts, including pending outcomes.

`SourceRecursiveIntersectionCompileSafetyCalls` derives safe Mu entry,
original physical reference lookup, guarded child requests, matched rows,
and ordered unions. `compileNode_safe` and `compileEdge_safe` derive safety
for every branch from the original valid physical inputs. No callback purity,
completed memo provenance, or product-language premise is supplied.

## Actual native observation adapters

`SourceRecursiveIntersectionNativeObservations` derives the actual source key,
published handle, captured completed cell, and unchanged physical/domain
machine from native lookup and demand. Direct selection retains its original
request and complete native state.

`SourceRecursiveIntersectionNativeSourceCalls.node_started_source` and
`edge_started_source` derive captured request identity, strong current source
and memo invariants, and the exact newly running cell. `node_ready_source`
and `edge_ready_source` derive current result availability/residency and
concrete stable guarded kernel replay from actual native completed hits.

## Exact completed-run correspondence

`SourceRecursiveIntersectionNativeMeaning.Meaning` records a finite stable
recursive kernel bound and the exact returned physical/domain machine.
The full compiler equations turn completed native body meanings into actual
guarded node and edge executions. Sequencing combines finite child bounds
without a purity assumption.

`SourceRecursiveIntersectionNativeBounds.Bounds` records the existing checked
machine-word ranges at memoized requests in the actual evaluation tree.
Direct placeholder calls need no memo key. This is an explicit resource
premise. No general supply-overflow or unbounded-machine theorem is proved.
It adds no semantic body-execution or memo provenance premise.

`SourceRecursiveIntersectionNativeCorrectness.Bounds.correct` proves the full
completed native source-code correspondence. Its inputs are an actual native
evaluation tree, its checked word bounds, source body code, derived physical
safety, and initial strong source/memo validity. Its outputs are final strong
validity, exact physical/domain growth, the returned record property, and
guarded kernel agreement at a finite stable bound.

New completion provenance is derived inside the induction. Each actual
compiled body gives its source kernel execution. The original input facts
and exact returned machine then give `Produced`. Running-cell retention keeps
the original cell for that completion frame. No `Produced` premise is supplied
at new finishes. Native bodies are not replaced with uncached callbacks.

`SourceRecursiveIntersectionNativeApi.native_node_correct` and
`native_edge_correct` start from actual bounded native completion and its
extracted evaluation. They derive the same value and exact physical/domain
caches as the guarded kernel, final strong memo invariants, result availability
or row residency, and a finite stable kernel bound. `native_node_produced`
and `native_edge_produced` derive concrete provenance from those actual native
runs. They require no supplied kernel execution.

`cold_node_correct` starts with the actual valid physical input cache and
empty native memo tables. The reserved empty domain is derived. It does not
assume existing completed memo entries, a warmup, or an uncached execution.
An actual completed native run and its checked word bounds remain premises.
Available open results can be recursion placeholders. Availability does not
assert closedness or a complete interned physical root.

## Next obligations

The least-request-bound measure, actual canonical-domain equivalence,
running-cell origin, active-bound lifecycle, and conditional native demand
progress are now proved in
[request progress](notes-recursive-intersection-request-progress.md).
Derive the body-limit invariant through every compiled continuation and use
it to construct finite native execution. Conditional busy exclusion does not
prove that invariant for the whole driver.

Derive sufficient first-run native bounds for the intended valid input scope.
Completed-run correspondence does not prove that every input completes.
Pending constructors and busy thunk observations remain distinct. General
open nested constructor completion is still an obligation. Carry explicit
machine-word bounds; do not turn resource premises into an overflow claim.

The physical input view, cached free-variable/closedness equations, finite
reachable input carrier, and actual structural ranks are now proved in
[physical input view](notes-recursive-intersection-input-view.md). Use those
results. Canonical representative readback, both independent copied-language
directions, the complete finite input interface, and sufficient semantic
schedule bounds are now proved in
[exact original inputs](notes-recursive-intersection-input-exact.md).
Connect the
actual source requests to the semantic schedule and obtain sufficient bounds.
Preserve exact constructor/domain effects and native memo publication.
Do not repeat completed-run correspondence or supply an execution trace as
a replacement termination proof.

Use actual child/row traces and canonical output readback to derive
`ProductReadback.members` and `.rejected`. `product_exact` then gives product
language. Do not supply equivalent product-row or language contracts.
Derive preparation of new Mu bodies, or a larger cold-exposure invariant,
before composing the cold table and Sized adapters. Concrete GHC primitives,
thread scheduling, and verified Haskell extraction remain open. The exact
Sized source paths and older constructor/equality work remain preserved.

## Validation

All nine new modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
aggregate build passes 1,252 jobs and 41,133 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-native-correctness-20261014-audit.log`.
No Haskell source changed. Prior Nix and formatter checks remain the source
validation checkpoint. Prior proof, draft, and fixture bytes remain preserved
against the saved manifest.
