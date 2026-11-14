Status: UNCOMPILED local helper draft. The final resource header is UNPROVED.
No compiler was run. No live source, Haskell, Git, or board was changed.
The packet contains source-only files. It contains no objects or build trees.

Proposed final statement

The exact target is target-header.lean.txt. It uses the actual input Packet,
Fits and Heap at the same caller and full Memos. It has no model, read,
check, ready, larger-budget equality, or successful-adapter supplier.
The prefix uses the actual selection decision and identity narrowing at all
six identical budgets. It preserves the original caller and query argument.
Stopped prefixes and parked prefixes with no cached adapter are explicit
exempt branches. A failed preparation is explicit too. Literal identity
narrowing cannot produce that preparation branch; this requires the local
prepareWithNarrow reduction, not an assumption on an external narrow callback.
The target does not assert CurrentPrefixResources on a stopped prefix.

Actual consumers

SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.lean:54-76 defines
the positive-depth expand arm. Only parked(Some cache, Some supported raw)
can restart. A stopped prefix or parked(None cache, any raw) reaches the last
wildcard. The result is exactly
  .stopped [] (.selected uv observed) (some (caller, queries)).
The private unsupported_prefix_stops draft states and proves this equation.
No child, restart, ordinary fallback, or subsequent output branch runs there.
The zero-depth expand arm independently returns
  .stopped [] (.exhausted uv metadata before) (some (caller, queries)).
runWithNarrow at106-120 only supplies the actual Restart.decision to resume.
With chosen = some(.expand uv), unfolding runWithNarrow and rewriting chosen
and the private equation gives the same stopped result for the actual entry.
The older SharedPreparedRecursive worker has the same wildcard at160. The
exact helper covers the generic active child-policy worker, including eager
and shallow instantiations. An outer consumer of the returned HookResult is
outside this local equation. This does not establish whole-CPS safety.

Existing public primitives

1. EnumerationExecution.getValue_moreFuel retains the same value and entire
   returned core after every larger representative bound. Combine it with
   EnumerationPartialExact.getValue_exact at BOTH bounds. The result is raw
   list equality, not just one successful member. This includes exact path
   compression. The first private draft helper proves this equality.
2. Native checkRepeated inspects the same heap before it reads a representative.
   In its recursive-boundary arm, success_bind exposes the actual successful
   representative call. EnumerationExecution.representative_moreFuel and
   EnumerationPartialExact.representative_success_exact at BOTH bounds allow
   bind_single to replace both actual reads by the same root and same complete
   compressed core. The remaining get/ancestry-test/optional setValue code is
   identical. The second private draft proves whole raw check equality for
   both repeated Bool values. No forest-totality premise is needed here.
3. SourcePruningEnumerationNativeIndex.write_some_moreFuel preserves the exact
   successful cached write. ParkedRestart.adapt only maps frame checked over
   that write. The third private draft proves exact adapter replay when the
   earlier actual adapter was Some. None is not inferred to remain None.

Remaining whole-prefix composition

This packet does NOT contain a complete whole-prefix replay proof. The next
local statement must prove that the nonexempt actual prefix at fuel is exactly
equal to the prefix at fuel+extra. Its hypotheses should be Ready/PendingRealized
and Total derived from the actual Packet, not success-stability providers.
Inspect the ACTUAL read list and check list in runPrefixWithNarrow. Unsupported
lists stop and are exempt. A nonexempt prefix therefore exposes successful
actual singleton pending read and singleton Bool check. Apply the private raw
replay helpers to those observations to keep handle, incoming SCS, readAfter,
checked core and Bool exact at fuel+extra.

If repeated=true, inspect the actual parked candidate. None is exempt. Some
replays exactly by parked_adapt_some_moreFuel. Its same-cache Restart.run and
complete parked raw receipt do not depend on these changing fuel arguments.
Do not replace a failed adapter by an arbitrary valid cached endpoint.

If repeated=false, derive Frame readAfter checked from the observed recursion
check using SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
with (getValue_frame ... total reading).1.total total. Its precise signature
takes heap, actual fuel/uv/handle/SCS, readAfter/checked, Total readAfter, and
the actual successful false check. See IdentityCompletion.lean:138-149 for the
existing exact application. runPrefix_identity_pending derives
lookup/encoding/closedness from this actual pending read, Ready,
PendingRealized, Total and that Frame. Apply this law at the old and larger
read/check bounds. Both decoded values are equal by deterministic lookup.
For Empty, both whole outcomes contain the same reject action and empty raw
list. For nonempty, both contain pure (), the same checked cache frame, the
same advanced actual caller, the same queries, and the same pure recordTypes
right callback with false and unchanged metadata. Encoding is the same old
handle, so no new representative read remains captured in the action.
No native heap changes. All six fuel arguments can therefore increase together.
The prepareWithNarrow identity branch cannot be .failed; keep the branch
explicit until this reduction discharges it.

Final resource transport

Only AFTER whole-prefix replay is proved, obtain bound from the existing
prefix_identity_complete_resources with checkEmpty=false and edgesOf=fun _=>[].
Those two parameters do not occur in runPrefix. Choose its extra=fuel, giving
resources at bound+fuel. New replay compares fuel with fuel+bound. Rewrite
Nat.add_comm to align the actual common budgets. Transfer CurrentPrefixResources
along the PROVED equality of whole outcomes. No assumption of completion at a
larger budget can replace this equality. The final resource target does not
need a new provider, model, caller, Memos, invariant, or input gate.

Proof boundary

The full resource target and whole-prefix equality are still unproved here.
Only the small helper/consumer bodies are drafted, and they are UNCOMPILED.
No global finite-witness, generated-type closure, whole outer CPS, or Haskell
correspondence claim follows from this packet. No Haskell fix was identified.
