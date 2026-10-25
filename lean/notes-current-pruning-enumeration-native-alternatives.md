# Ordered native alternatives with enumeration rollback

## Current result

Worker and transport: `a3b400c4f2cc2146368d37e5f80ec4d2152c7637`.
Admitted completion: `e8bcb10c65090595572c6edc930ad52a20f624a6`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

`SourcePruningEnumerationNativeBranchCompletion.complete` derives sufficient
common finite bounds for an ordered serial scan of selected ordinary edges.
Each alternative starts from the same captured enumeration cache. The next
alternative uses the reached native caller and saved queries. A valid child
rejection retains its native effects but does not supply its enumeration
cache to the next edge. Successful receipts retain their actual finalized
cache. No aggregate final enumeration cache is constructed.

The scan stops explicitly at unsupported preparation. If every selected edge
that passes the arity check has a supported annotation, the scan completes
the whole list. Its processed receipts include successful edges, arity
rejections and valid child rejections. Completion of the scan does not mean
that every edge succeeds or that any term is accepted.

## Runtime boundary and traces

`NativeBranches.advance` permits exactly three continuation forms: complete
edge output, arity rejection, and raw-empty child rejection with an actual
cache. It extracts only the reached caller and query map.
The recursive call uses the identical original `before : Cached` value.
It retains edge order and duplicate occurrences.

The aggregate result contains either all processed receipts and the final
native endpoint, or a processed prefix and the exact first noncontinuable
captured-edge result. `uncached` and `not_continued` are unconditional laws
at fixed bounds. They do not run the suffix.

An outer `none` from `CapturedEdge.run` remains explicit. That existing result
does not contain the caller or cache reached before a failed finalization.
The new worker does not invent those fields. Faults, malformed streams,
missing caches and unsupported preparation remain explicit stops outside
admission. The admitted theorem excludes all such stops except unsupported
preparation, which it retains as `some .unhandled`.

`NativeBranches.Trace` records every actual captured-edge call and continuation
at the same fixed bounds. The two trace laws relate completed worker results
to these exact traces in both directions. Every receipt contains its own
branch cache. Trace does not merge those caches or reset native state.

## Admission and transport

Initial premises include current caller `Context`, selected-slot `Ready`,
an actual stored pending handle, and its exact decode to the ordinary parent.
They include pending-value realization, root paths, canonical waiting counts,
native expandable flags and inherited `InputsPending`. Every selected edge
belongs to that parent's stored edge list. These premises match the existing
captured-edge completion producer.

`NativeGrowth.flags` transports every valid native flag of an unchanged cache
through `SourceEqualityRequiredCache.Keeps`. A valid old flag excludes an
unresolved old handle. `lookupNode_keeps` retains each actual decode.
Heap growth alone is insufficient: `Keeps` also retains issued history.

After a continuable head, the proof retains the original enumeration cache.
Its safety, roots, counts, stored-slot equation, bounds and pending conditions
therefore stay exact. Existing realization transport with a reflexive frame
and the new flag theorem establish the native-facing cache facts at the
reached heap. The original parent decode transports too.
The head's actual `Post.context` supplies the next caller context.
Full Memos and inventory values remain proof witnesses. The runtime retains
the actual caller and query endpoint exposed by the existing receipts.

`Ranges` requests selected-edge numeric admission at the current caller and
original enumeration cache. It requests suffix numeric admission only after
an actual continuable captured-edge call. It quantifies fixed execution
bounds and reached endpoints. It supplies no future successful trace, cache
correctness or caller context. The completion producers derive those facts.
Initial-only numeric admission remains open.

Representative, native and index-fuel bounds combine by addition. The p/h
bounds combine by maximum. Every larger admitted common bound gives the
same result. Actual head and tail `Post` values compose.

## Receipt certificates

`CacheValid` records roots, storage, native pending-value realization,
canonical waiting counts and all-slot native flags for one cache at one caller.
`Admitted` retains these facts for each processed receipt. Complete receipts
also retain `Safe`, a bounded fragment, the exact captured-slot enumerated
value, empty expansion ancestry and target rootness. Valid child rejection
does not gain an unconditional `Safe` claim.

Each receipt's certificate refers to its own reached caller heap. This is
not a theorem that every earlier receipt has already been transported to the
final caller heap. Such transport remains available as a separate operation.
The final `Post` retains the actual physical native effects, merge extension,
fourth-table extension and final context. It does not assert extension of
every query or unfolding memo family. The actual returned query map is
threaded, and its final equality is retained.

## Verification

All three final modules pass Lean 4.34.1 with all linters and warnings as
errors. Eight strict attempts are retained. Native growth passes immediately.
Worker attempt 1 exposes a reserved identifier. Attempt 2 passes. Attempt 3
adds fixed-bound missing-result and noncontinuation laws and passes.
Completion attempt 1 exposes a Boolean lemma name, fuel normalization and
dependent match elaboration. Attempt 2 leaves a local result equality.
Attempt 3 adds supported-annotation completion and exposes a reduced None
equation. Attempt 4 passes.
No linter or production proof-resource limit is disabled or increased.

Installed builds and all eleven public declarations pass. The full public
log has 250 lines, 16506 bytes and SHA-256
`c15456537e7739e8466908a40f8cebb0dc382012fcf4306dfa97c504661ffe27`.
All axiom sets are subsets of `propext`, `Classical.choice` and `Quot.sound`.
The aggregate Audit passes with 3746 jobs and 76695 theorem dependencies.
The older unused `inputs` warning remains unchanged.
Checks run serially under 4 GiB heavy-management caps with no swap.
Full attempted sources, raw logs, reports, final sources and peak records
remain in `restart-evidence/20261025-native-alternatives`.
Source review finds no semantic blocker.

No Haskell source changes or runtime tests. The external Haskell repair
handoff remains first in root FINDINGS. The optimized interned core, earlier
native workers, historical repairs, counterexamples and constructor/equality
work remain unchanged. H6's source remains unchanged.

## Next work and strongest claim

Compose actual selected entry with this alternative worker in the ordinary
parent wrapper. Keep readiness at the actual entry boundary. Account for
native normalization, narrowing and oracle calls at their actual positions.
Derive global pending-reference and fragment-dependency history facts.
Transport or interpret earlier receipt caches at the final native heap where
the next semantic layer needs it. Connect successful receipt extraction and
whole-driver finite-tree language semantics.

This worker chooses serial forcing of alternatives. Haskell's process-global
memo tables and lazy result thunks do not establish this exact effect order
for arbitrary demand. Full raw-stream erasure and Haskell demand correspondence
remain open. The old independent shallow branch theorem remains separate.

H6 remains the strongest end-to-end result. Covered closed construction,
valid initial constraint cache and original allocation history, any prescribed
finite budget and number of modeled node calls derive sufficient finite fuels
and one mathematical width chosen after construction. With empty inherited
payload, the final available value has exactly the original finite-tree
language under the formal formula and entailment interfaces.
Arbitrary mixed calls, whole typing/pruning, withoutRedundantEdges, concrete
solver correspondence, extraction, physical maps and machine integers,
practical resource bounds and convergence remain outside that claim.
