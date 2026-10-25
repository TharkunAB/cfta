# Native cache certificates after concrete fragment callbacks

## Current result

Proof commit: `faec19a56`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55` after fetch.
The whole formalization goal stays ACTIVE.

The actual concrete Left callback endpoint now retains the native indexed
cache, captured-fragment certificate and dependency history. It also retains
suspended-reference history when the original receipt supplies that history.
The existing selected-ordinary producer supplies the original history.
Its entire source remains unchanged and inherits the stronger completion
predicate through its existing proof call. No runtime worker changes.

## Cache transport uses actual safety and exact root paths

NativeCacheFrame.cacheValid_frame accepts the original CacheValid, an actual
compression Frame and separately Safe after. It retains the same root map:
each stored root path follows Frame.reaches. StorageValid comes from Safe.
PendingRealized follows exact slot equality at the same native Caller heap.
Canonical waiting counts and native candidate flags follow exact values.
EnumerationExpandableIndex.frame retains the original waiting map and flags.

Frame alone does not establish Safe. An explicit entry beyond the allocation
counter can preserve effective root paths and still violate the forest bound.
The concrete callback's actual RenderStable.safe supplies the needed safety.
No new Safe assumption is added to the callback producer.

admitted_complete_frame retains the full successful receipt certificate:
CacheValid, Safe, bounded fragment, the original captured-slot fragment,
empty expansion ancestry and the captured raw root. Counter, values and
ancestry follow the same frame. The actual self-root path retains its size.
fragmentHistory_complete_frame retains original-to-final allocation growth,
actual pending targets for all fragment holes and conditional frontier+1.
The same frame transports actual targets and the existing dependency levels.
pending_complete_frame retains suspended-reference history with the existing
frame_pending theorem. It does not require a new oracle property.

These outputs use a reframed complete constructor as a certificate. They
do not claim that CapturedEdge.run returned the cache after the later callback.
The original callback action and its actual endpoint remain explicit.
Caller and saved query fields stay those of the original branch receipt.

## Pure selection and updated metadata

selection_frame proves exact next selection for any fixed preference after
framing a new core with the original indexes and allocation counter.
The candidate list uses List.range counter. Unchanged indexes alone are
insufficient; actual counter equality is also used. The lemma needs no
Graph, Safe, values or representative-class premise.

Apply it with the preference built from the callback's returned metadata
on both sides. The callback updates type positions and pending matches,
so its metadata can change an expansion order. This theorem does not equate
preferences built from old and new metadata. A true callback pruning result
still terminates its branch in the source. Selection equality is a state
property, not a proof that a rejected branch performs another selection.

## Strengthened existing completion output

ReceiptCallback.Completes retains its exact declaration type and inputs.
Its output predicate is strengthened. At the same actual callback result it
now includes Admitted and FragmentHistory for the reframed cache, conditional
Pending transport and pure next-selection equality for every fixed preference.
The earlier Success, RenderStable, Frame, Stratified, exact metadata fields
and returned pending-ID bounds remain in the output.

The completes theorem retains its exact declaration type. It calls
recordTypes_inl_complete_bounded exactly once, with the same arguments and
same chosen fuel, metadata result and final cache. The new conclusions are
derived from that existing witness and its actual safety and frame.
There is no callback-success premise, new admission input or second execution.

SelectedOrdinary.complete_with_history already returns Completes for every
processed receipt. The stronger result therefore reaches original selection
without changing that producer, its wrapper, its original Pending history,
its ordinary node gate, its numeric Ranges or any reached Caller endpoint.
The independent per-receipt callbacks still use the supplied branch metadata.
Sibling metadata is not folded: each returned metadata value belongs to its
own recursive continuation. Exact native effect interleaving remains open.

## Verification and evidence

Lean 4.34.1 checks both changed modules with all linters and warnings as
errors. Three strict attempts retain one failed first helper check: unfolding
selection leaves a reflexive goal, which the final rfl closes. The final
helper and concrete callback checks pass. The installed helper build passes.
Aggregate Audit rebuilds the unchanged selected consumer and passes with
3767 jobs and 76842 theorem dependencies. Audit source remains exact.

Installed public readback checks ten declarations and their axiom sets.
It also prints the full installed Completes definition to expose its new
output clauses. The full output has 969 lines and
99336 bytes. Its SHA-256 is `a88d6ad045858354d988600306f09d6f3c379bbefce4b97fa9db11ebcc564f57`.
There is no output ellipsis. All axiom sets are subsets of propext,
Classical.choice and Quot.sound. The earlier unused inputs warning is
unchanged. All six checks run serially under heavy-management 4 GiB caps.
No Haskell source or package file changes, so its suites are not repeated.

A separate source review confirms the safety boundary, original Caller and
query fields, actual callback endpoint, fixed-preference quantification and
reframed-certificate meaning. It finds no new future-success premise or
claim that the driver continues after callback pruning.

Evidence: lean/restart-evidence/20261026-native-callback-cache.
The manifest records exact payload bytes and SHA-256, including raw logs,
strict source copies, failed attempt, public definition readback, final and
original source snapshots, proof diff, verification report and cap records.
Force-add exactly the manifest payload list and verify committed bytes.

## Next work and claim boundary

Compose the actual callback Boolean with the source branch decision. A true
result rejects. A false result restarts selection using returned metadata
and the actual framed native cache. Retain all native cache and history
certificates through that continuation. Do not assume the old metadata's
preference equals the updated metadata's preference.

The repeated-recursion path clears its bucket and restarts without narrowing
or an oracle call. Its actual indexed-cache receipt is already available;
connect it to the same scheduler step while preserving branch-local metadata.
Exact depth-first native effect and recursive-continuation interleaving,
initial-only native query capacity, native Graph/heap correspondence,
terminal/nonordinary outer fallback, pruning language laws, extraction and
complete finite-machine/Haskell correspondence remain open.

H6 constructed_node_calls is unchanged and remains the strongest end-to-end
language theorem. It covers closed construction, valid initial constraint
history, any prescribed finite budget/rounds, derived finite fuels and one
mathematical width chosen after construction. It preserves the original
finite-tree language under the formal formula/solver interfaces. It does
not prove the whole typing/pruning enumeration driver.
