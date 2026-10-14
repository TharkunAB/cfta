# First-order recursive construction and prepared shared rows

Checkpoint: `e9214aa6`, upstream `f59c198d`, 2026-10-14.

## Actual source construction

`InternedFreshOrdinaryFirstOrderCompletion.binder_complete` proves repaired
first-run completion for one binder with an arbitrary binder-free body.
The body can contain finite constructor trees, unions, and captured values.
The proof follows both actual probes, the selected fresh ordinary level,
cache hits, reservation, the actual body callback, and first-writer completion.
It does not assume an earlier completed construction.

`InternedBinderFreeDepthBound` proves that binder-free construction cannot
increase the maximum input depth. It includes ordered child and edge effects,
normalization, and self-reference filtering. This is a depth bound, not a
general theorem that predicted depth implies completion.

`InternedFreshOrdinaryFirstOrderHeap.binder_shallow` derives the stored-body
invariant from depth-zero captured inputs and an initially shallow cache.
`closed_prepared` starts with empty caches and derives actual completion,
coherent facts, payload availability, and `MergedPhysicalWarmup.Prepared`.
No prepared-heap or stored-knot premise remains for this construction fragment.

The source correspondence is the repaired binder probe protocol in
`cfta/src/Data/CFTA/Interned/Type.hs`. Stored reconstruction uses no new
binder requests in this fragment. Its repaired and earlier executors therefore
have identical values, failures, and cache effects.

## Actual cold row exposure

`SourceFirstOrderExposure.source_read` derives finite cold `nodeEdges`
execution from the actual constructed result. It retains the returned cache,
growth, issued-map history, absence of new Mu records, resident closed edges,
stable additional fuel, exact edge origins, and original guarded language.
This includes raw and smart outer binders. Arbitrary guards remain data.

The reader follows `Interned/Operations.hs:nodeEdges`: ordinary direct reads,
the direct ordinary result of Mu unfolding, and canonical edge-identity
ordering for the union-closure fallback. Unresolved references, pending
construction, and exhausted proof fuel remain distinct outcomes.

## Fixed prepared shared traversal

`MergedPreparedReaderEffects` proves that every row read in a `Ready` cache
retains that exact cache, for every fuel and every outcome. Finite inventory
warmup derives `Ready` and retains its available unfolding results.

`SourcePreparedSharedRows` reads the actual issued map and canonical payload
map. Mu, union, and ordinary values retain their identities. Empty values
use the separate empty state. Open probe records have no exposed rows.
Each selected row list has a finite stable source execution witness. The
selection is a proof construction with `Classical.choose`.

The actual issued counter bounds every outgoing child identity. It supplies
a finite closed domain for `SourceInternedRows.toRows`. Traversal preserves
the source worklist order. Table keys use ascending identities. Every copied
edge retains its symbol, constraint, and ordered child identities.

`SourcePreparedSharedRowsLanguage.language_exact` proves the shared graph's
exact physical epsilon language for every closed available root, including
cyclic Mu and union records and arbitrary guard interpretations. Its proof
uses actual row exposure and induction on finite terms.

`SourceFirstOrderSharedRows.source_rows` derives construction, warmup, finite
shared traversal, and original guarded language without a supplied cache.
`source_sized` composes this result with the reference Sized recurrence. It
proves exact distinct node-count classes, finite evaluation at every size,
distinct size-order prefixes, exact bounded coverage, and both rank/unrank
inverse laws for the constructed graph.

## Exact limits and next target

The construction body contains no nested binder request. General nested
binder completion and cached-depth heap induction remain open. The prepared
shared-row theorem accepts arbitrary prepared resident records; deriving that
preparation invariant for all source syntax remains open.

Warmup is explicit. The source `reachable` function does not run that warmup
before its cold traversal. These proofs do not equate the two allocation
orders or their raw tables. The stateful cold shared walk now has exact
finite execution and exact final-table language under `Prepared`. The new
`SourceFirstOrderColdSized` derives that premise from actual construction and
proves the full reference Sized laws through actual cold rows, without warmup
or a supplied trace. Native and encoded solver-decided public queries now
compose with those rows. See [the cold worklist note](notes-cold-shared-rows.md).
Native cyclic product construction and general open nested binders remain open.

The first-order Sized composition uses the returned row order. The existing
finite-map proofs establish canonical reference, solver-decided, and optimized
dispatch sequences after their actual validation and preprocessing. They do
not imply that warmup preserves native cold identity tie order. Custom-key
ties retain the existing qualification.

Concrete Haskell containers, lazy heaps, external SMT and PRNG behavior, and
verified extraction retain their stated boundaries. The optimized interned
core is unchanged.

## Validation

The aggregate Lean 4.34.1 build passes 1,204 jobs and checks dependencies of
40,032 theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted. The first-order and cold worklist modules are in `MicroCFTA/Audit.lean`.
Log: `/tmp/mcfta-cold-complete-20261014-audit.log`.
No Haskell source changed in this checkpoint. The earlier 640 passing Nix
examples and formatting checks remain the current source validation.
