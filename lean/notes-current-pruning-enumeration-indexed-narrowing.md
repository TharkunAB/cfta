# Indexed caches from actual native narrowing

## Current result

Replacement and reads: `9d4de2db2`.
Narrowing producer and Audit imports: `04a5ba6d0`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

Actual pending-handle replacement now derives the native expandable flag,
exact canonical waiting counts, safety, root paths, realized pending values
and reference history at the same written enumeration cache.
Actual native narrowing now derives that cache for each nonempty result.
Empty rejection, an equal handle and a changed handle remain distinct.
No old producer contract or runtime worker body changes.

## The full source write

Enumeration.hs:436 reads the old slot and passes its entire suspended bucket
to writeUVarValue as lost references. It passes the entire new bucket as
gained references. A narrowed handle keeps the same bucket. The native model
therefore executes write with gained=scs and lost=scs. It does not execute an
empty differential update in place of that source operation.

Replacement.count_cancel proves that subtraction and addition retain a
canonical sparse map. It counts every occurrence after mapping variables to
their current roots. Repeated occurrences and variables in one class remain
counted. Canonicality matters: an arbitrary some 0 entry can become none.
The genuine initial count invariant supplies the required canonicality.
One derived finite root-lookup bound covers both folds at every larger fuel.

Replacement.complete retains the supplied actual setValue endpoint.
It derives a native write run with both full buckets and exactly that core.
The target flag is recomputed from the new decoded value and current bucket.
It need not equal the old flag. Native Keeps transports all other flags.
The final waiting map equals the initial map as a proved result.

Initial Safe and the stored pending equation derive a live root and bounded
replacement bucket. The actual plain write then retains Safe. Initial
realization, Keeps, and the new decoded closed available value derive final
realization. The write creates no new enumerated slot. It preserves incoming
reference conditions for every held variable and global pending history.
It also preserves Ready when the original target is Ready.
Ready does not assert that the new expandable flag is true.

## Actual reads and the narrowed result

Replacement.after_read uses the actual value read and representative reread.
It derives that the reread root equals the selected variable. It obtains
safety from the actual read theorems, not from an arbitrary compression frame.
The complete frame transports paths, values, counts and old flags to the
reread cache. The replacement theorem then derives the same actual write.

NarrowCache.complete calls Action.prepare_pending_complete once. It uses
entry=readAfter and the reflexive entry frame. It keeps that producer's old
value, narrowed result, native fuel, next heap and encoded handle.
The existing inputs are genuine initial native readiness, enumeration Ready,
realization, paths, exact counts, native flags and an actual value-read receipt.
No final cache invariant or successful narrowing action is supplied as an input.

An Empty result retains the actual reject action and has no successful final
enumeration state. An equal handle retains the pure action and the framed
actual read cache. A changed handle retains the producer's representative
reread, actual plain write and final core. The native write equation derives
the index cache for that core. The returned action is still the complete
representative-and-write action. No new final-state witness replaces it.

Every nonempty case derives Ready, paths, realized pending values, the new
stored-slot equation, exact waiting counts and all native flags. Initial
pending and incoming history remain conditional outputs at that same cache.
The theorem derives a model native heap. It does not construct a full checked
Caller or a Context/Post receipt for its memo tables and inventory.

## Verification and approaches retained

The two new proof modules and changed Audit imports pass Lean 4.34.1 with all
linters and warnings as errors. Nine strict attempts are retained. Five fail:
the first replacement attempt needs explicit count buckets and the old-slot
bound; the next needs the phantom slot symbol type; one spelling conflicts
with local Symbol notation; the next needs Option constructor injection and
an explicit history function. The final replacement attempt passes.
Adding actual-read composition passes its first attempt. The first narrowing
cache attempt needs the final core equality applied to the whole packet.
Its second attempt passes. The strict Audit check passes too.

Two installed helper builds pass. The aggregate Audit passes with 3752 jobs
and 76721 theorem dependencies. Installed public readback checks seven
declarations. Its full output has 364 lines and 30448 bytes. Its SHA-256 is
`4c70877f091810000fb579dd933fa83c01ac0a215b52ea1a4ac10b1597dafa2d`.
Every axiom set is a subset of propext, Classical.choice and Quot.sound.
The older unused inputs warning remains unchanged. All thirteen checks run
serially under 4 GiB heavy-management caps with no swap.

All attempted compiler inputs, full raw logs, reports, final sources, cap
records and the proof patch remain in restart-evidence/20261025-native-replacement.
Earlier public contracts and runtime workers remain unchanged. Audit adds
only the two imports. No Haskell runtime code or suite changes. No new
Haskell defect or repair is found. Root FINDINGS retains the external handoff.

## Next work and strongest claim

Compose the native indexed narrowing producer with actual selection and
ordinary entry. The existing selected ordinary theorem is a same-cache
theorem. Do not rerun its selection premise at the narrowed cache: the new
candidate flag can differ. Retain the old actual selection and transport
Ready and IncomingAvoid through the actual prefix instead.

This narrowing theorem has no intervening repeated-recursion check or
callback between its first read and action. Integrate actual recursion
bookkeeping and the concrete typing callback at their reached states.
The concrete pre-expansion callback is already pure. Rendered callbacks
have a full compression frame. A frame alone does not establish Safe.
Ordered activation refreshes and arbitrary callbacks need actual contracts.

The native narrowing computation must also connect to the full checked Caller,
memo tables and inventory required by ordinary completion. The heap Keeps
receipt alone is not the complete Context/Post producer. Machine-counter
correspondence and initial-only resource admission remain separate.

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache and original allocation history, and
prescribed finite budgets and modeled node-call rounds derive sufficient
finite bounds and a mathematical width chosen after construction.
With empty inherited payload, the final available value has exactly the
original finite-tree language under the formal formula and entailment
interfaces. The whole typing and pruning driver remains outside this claim.

Fragment-hole history, acyclicity, successful extraction, terminal parents,
parent normalization, whole-driver language semantics, arbitrary Haskell
demand, full raw-stream erasure, concrete solvers and physical runtime
correspondence remain open. No practical resource or convergence bound follows.
