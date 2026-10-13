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

`InternedPendingLiveMismatch.closed_live_mismatch` now selects a different
pair of ordinary names at a live position of the encountered binder. Its
route uses the exact earlier and current lexical input lists. The abstract
atoms retain distinct position indices even when reference pairs repeat.
A live fresh name
would occur in the old Depth probe and violate its identity bound. This
excludes fresh inputs and the active ancestor's own fresh local from the
witness. The selected ordinary crossing retains its source body, position,
actual computed level, and chronological cache history.

`closed_live_depth_mismatch` retains the two completed Depth calls of that
same source body. Their depths differ. The later ordinary name belongs to
the active ancestor's original Depth probe and is already a live captured
input of the ancestor. It therefore occurs in the ancestor's original input
list. If its level differs from the ancestor's original computed level, the
name also occurs in the original ordinary probe. Both key components are
the actual completed probes retained by the active source origin.

The remaining case must account for this ordinary alias with a live capture
outside the active ancestor. A fresh-only change can alter a computed level,
as the checked fixture shows. The new theorem requires the changed later
level to occur in the ancestor's original captures and original Depth probe.
Neither the level-change fixture nor the live-mismatch theorem establishes
a pending counterexample. General closed no-pending remains open.

Pinned Lean 4.34.1 builds `InternedPendingLiveMismatch` in 274 jobs. Its
isolated dependency audit checks 9,203 imported theorems and permits only
`propext`, `Classical.choice`, and `Quot.sound`. No Haskell source changes.

`InternedPendingOrdinaryOrigins.closed_capture_depth_mismatch` now derives
the earlier introduction of the aliased ordinary capture from the stopped
closed source execution. The witness retains three completed Depth calls:
the two same-body calls with different depths, and an enclosing call whose
depth equals the later depth. The enclosing call finishes before the active
ancestor's original source start. Its captured input list is strictly shorter
than the ancestor's captured input list. All three calls retain their actual
source contexts and cache histories.

The proof carries ordinary introduction histories through actual Depth,
ordinary, and fresh entries. It preserves them for each active reservation.
`encounter_live_mismatch_of` retains this extra origin invariant during live
mismatch extraction. The existing live-mismatch statements are unchanged.
The shorter input list is a lexical bound. It does not prove that the same
mismatch recurs at that shorter source context. That additional decrease
obligation remains open. The isolated origin audit checks 9,219 imported
theorems against the same three permitted axioms.

`InternedOrdinaryCaptureBoundary` checks a further limit on this argument.
Its closed expression retains an extra ordinary capture in an ancestor's
union. At slot 93, the inner Depth level changes from zero to one, and
Unint 1 already occurs in the ancestor's original Depth-probe free set.
`closed_alias` proves these observations by kernel reduction. `complete`
proves that the whole closed run completes. All references are in lexical
scope. Thus a changed ordinary level can alias an original live capture
in closed execution. This example does not reuse the pending ancestor key
and does not refute the no-pending claim. A proof must use more than the
changed level and its membership in the original probe.

`InternedPendingJointKey.closed_site` retains both exact old probe records
at the same current source site. The current Depth callback returns the
ancestor's original Depth value. The current ordinary callback uses that
value's actual depth and returns the ancestor's original ordinary value.
`Site.capture_equivalent` decodes both observations and proves equality
of all live captured-name memberships, including Depth and the original
ordinary sentinel. It does not discard either key component.

`InternedPendingJointKeyMismatch.closed_joint_mismatch` keeps this site,
its actual earlier completed representative, both earlier callbacks, the
live changed position, and the shorter producer history in one witness.
The earlier pair already has a complete record at the ancestor's missing
reservation cut. At least one of its two reference components must therefore
differ from the ancestor's original pair. The current pair equals both
ancestor components exactly. This is a stronger restriction than the old
free-name support witness. It does not yet transport the mismatch to the
shorter producer context.

`InternedPendingJointKeyBoundary.closed_different_pairs` checks the concrete
closed alias example. Both actual inner probe references differ from the
ancestor's original references at slot 93. The fixture satisfies the ordinary
support observation but not the exact joint-key premise. General closed
no-pending still requires excluding the full joint-key mismatch witness.
