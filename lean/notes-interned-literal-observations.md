# Full source observations permit arbitrary literal aliases

`InternedLiteralObservations.build_empty` and `callback_empty` compare
actual complete full-syntax executions. Literal lexical inputs of equal
length give the same EmptyNode decision. The inputs can contain arbitrary
aliases. The theorem requires the constructor invariants at each actual
starting prefix. Closed source execution derives those invariants.

`callback_self_forward` and `build_self_forward` cover both normalized
callbacks and raw body execution. If the first supplied local is absent
from its captures and the first result is exactly that local, the target
result is its supplied local. The target local can equal a captured name.
There is no injective-name-map premise and no assumed callback relation.

The proofs use the full source profile theorem. A direct fresh-local result
forces the symbolic body to have no captured root reference and to use its
argument. The constant-name map preserves and reflects this class under
all equal-length literal input lists.

These observations supply the empty and bare-local parts of paired source
execution. Exact identity under boundary absence still needs the dynamic
recursive-request argument. The observations do not prove that argument.

Exact ordered root-profile correspondence is too strong. A temporary
kernel-checked fixture executes two smart binders under `[Depth, U0]`.
The first body returns its captured variables in their original order.
The second returns them in reverse order. Both request the Mu key
`(U0, Depth)`. The second call returns the first complete representative,
whose root profile is `[Depth, U0]`. The pure interpreter for the second
body returns `[U0, Depth]`. The existing set-based `Equivalent` theorem
holds. Exact list equality does not hold. Both actual calls complete.
This is a proof boundary, not a source termination counterexample.

`InternedFreeAbsenceReplay.build_related` now proves full raw source replay
when one changed interned name is absent from the first result's free set.
Both compared calls must have completed in a common coherent cache. The
recursive case reads absence from both actual request probes. It then
compares the smaller source bodies and reuses the canonical request.

`InternedFreshCallbackBoundary.callback_clear_of_raw_absent` transports
boundary absence from an actual fresh callback to an actual sentinel
callback when the raw fresh body omits its local. It permits target aliases.
It does not require equality of the two filtered callback results. The case
where the fresh filter deletes a root local from a union remains separate.

`InternedLiveInputReplay.build_same` compares several changed lexical inputs
at once. Abstract atoms identify the input positions before actual reference
aliases occur. The pure free-name interpreter selects the live atoms. Only
those atoms must have equal references. The full mutual proof also compares
ordered child results and surviving edge records. The binder step compares
both actual normalized probes and then reuses the complete request.

`InternedLiveInputReadiness.not_pending_after_probes` uses an earlier completed
binder and the later call's two completed probes. Agreement on live inputs
excludes the later missing-record condition. It does not assume that the
later binder completes. `InternedLiveInputSupport.not_pending_of_fresh_changes`
derives that agreement when every different lexical input is a fresh interned
name and the later depth probe was already available before those names.
`InternedLiveSiteReadiness.site_not_pending` obtains the earlier binder from
an actual completed enclosing trace and a chosen Depth/ordinary route. Its
remaining comparison premise pairs the two literal name lists: each pair
is equal, or its later name is fresh. The route retains each actual ordinary
level. It does not replace ordinary locals by Depth.

`InternedPendingSourceOrigins.closed_encounter` now derives the active
ancestor's source body and captured inputs. Its origin retains the completed
raw Depth-body call, both normalized probes, the missing reservation cut,
and the earlier available probe records. Its descendant path records each
actual Depth, ordinary, or fresh callback entry and the corresponding cache
growth. The proof follows the actual stopped source execution.

`InternedActiveSourceReplay.Origin.completed_representative` obtains an
earlier completed source site from that origin. It keeps the same source
body and probe choice at each position. It selects Depth for fresh entries.
`Crossing.interned_after` proves that each crossed fresh name is at least as
new as the active ancestor. It does not classify ordinary locals as fresh.

`InternedPendingOrdinaryMismatch.closed_mismatch` proves a necessary
condition for a pending closed run. Its actual path and earlier source
representative must contain corresponding ordinary entries with different
computed levels. `closed_depth_mismatch` exposes the two completed Depth
callbacks of the same source body, their full source contexts, their unequal
cached depths, and their ordered cache histories. These are derived source
witnesses, not assumed callback laws.

General pending-site exclusion remains open. The remaining case concerns
different ordinary levels that still produce the active old probe key.
The old final probe alone does not show that all crossed locals are absent.
The existing closed probe-cost fixture has body/probe depths `(1, 0, 0)`.
A general equality between those depths is therefore false. No theorem here
assumes equal ordered profiles or equality between a stored body and either
one of its probes.

Pinned Lean 4.34.1 builds the pending ordinary-mismatch target in 273 jobs. The
isolated checks for full live-input replay and pending-readback exclusion
use only `propext`, `Classical.choice`, and `Quot.sound`. These modules
change no Haskell source.

`InternedOrdinaryLevelBoundary` rejects a stronger proposed shortcut. Its
`different_actual_levels` follows the actual outer probes and missing
reservation. The same inner Depth callback sees captures `[Depth, Depth, U0]`
and `[interned 9, Depth, U0]`; its cached depths are zero and one. The closed
embedding retains nested probe depths `(1, 0, 1)` at slot 28 and completes
with an empty root. These computations are kernel checked. Thus a fresh-only
change of captured names can change a computed ordinary level even in this
source construction. It is not a pending counterexample.

A bounded Python mirror search built from that fixture checked 14,916
variants, skipped seven for resource limits, and observed 12,903 traces with
level changes. It found no pending readback. This is finite diagnostic
evidence, separate from the Lean proofs. The temporary implementation and
log are `/tmp/mcfta-pending-level-search.py` and
`/tmp/mcfta-pending-level-search.log`.

The next proof target is a live ordinary-level mismatch. The current
`closed_mismatch` can select a changed ordinary input that the encountered
binder does not retain. Live-input readiness should strengthen that witness
to a different pair of ordinary names at a live lexical position. The later
name must then belong to the actual old Depth probe's free set. Compare this
name with the active ancestor's original key. Do not assume that all computed
ordinary levels are equal; the new checked fixture refutes that premise.
