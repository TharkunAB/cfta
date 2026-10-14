# Actual native constructor coverage and repaired pending encounters

Proof checkpoints: `83d79a1d`, `f79d0417`, `4ca51381`, `0b123bab`,
`3da93bb3`, `8a922c58`, `74fe5ef0`, `939a3499`, and `878cc5d7`.
Upstream: `f59c198d`, 2026-10-14.
Read [finite native observations](notes-recursive-intersection-native-finite.md)
and [actual optional binders](notes-recursive-intersection-maybe-mu.md).

## Coverage through arbitrary repaired nested construction

`InternedFreshOrdinaryCoverage.build_covered` covers arbitrary repaired source
syntax. It includes both raw and smart nested binders. A completed build
retains its incoming pending-key allowance. A fresh reservation adds only
its own key. Completion installs that payload and removes the extra allowance.
The mutual proof retains the actual order of members, edges, and children.
`callback_covered` covers arbitrary normalized body callbacks.
`closed_covered` starts from an actual completed repaired build in empty caches.

These are conditional coverage laws for returned values. They do not assert
that a build or callback returns. No `PreparedWithoutMu` premise is used.
The older executor, its counterexamples, and its coverage proofs remain.

`SourceRecursiveIntersectionMaybeMuCoverage` proves validity and physical
growth for the actual stored substitution callback, both probes, canonical
request, and optional-binder call. These laws hold on returned and pending
outcomes. `callback_covered`, `construct_covered`, and `maybeMu_covered`
retain coverage on every actual return. They require valid constructor caches
and incoming coverage. They do not require body preparation, assumed callback
termination, or whole-body lexical equivalence.

## Coverage at actual native source sites

`SourceRecursiveIntersectionNativePrefixCoverage.step_yielded_covered` proves
that one actual yielded native step retains valid constructor caches and
incoming payload coverage. Ordinary work uses actual interning. A returned
optional binder uses its actual coverage theorem. Domain operations, reads,
memo lookup/demand, and finish instructions do not change the constructor heap.
`Steps.covered` composes this result through every finite yielded prefix.

This prefix theorem needs no native completion, preparation, checked words,
structural memo invariant, or completed memo provenance. It preserves an
arbitrary incoming pending-key allowance. Complete coverage uses the empty
allowance. It does not claim complete coverage after an unfinished constructor
has made additional reservations.

`SourceRecursiveIntersectionNativeConstructorSite.step_constructor_site`
derives the unique instruction form that can report a constructor block.
`constructor_trace` starts from an actual bounded blocked result and derives:

- A finite yielded prefix shorter than the supplied native bound.
- The original optional-binder pair, body, and continuation.
- The exact pre-call native state and constructor heap.
- The actual source `maybeMu` pending equation.
- The exact remaining code and returned heap, with unchanged memo tables.

No source-site witness is supplied. Native busy and absent observations have
different constructors and cannot satisfy this statement.

`constructor_trace_covered` derives coverage at that original pre-call heap.
`constructed_prefix_covered` and `constructed_constructor_site` derive the
initial coverage from actual repaired source construction in empty caches.
The source construction may contain arbitrary nested binders. The premise is
its actual earlier completed build, not completion of the native intersection.
For an arbitrary supplied heap, incoming coverage remains explicit.

## Exact internal phase of a pending optional binder

`SourceRecursiveIntersectionMaybeMuPendingPhase.request_pending_fresh` proves
that a canonical request in a complete cache cannot report an incomplete hit.
A pending request must allocate on a genuine miss and stop in its fresh body
callback. It retains the actual reservation and callback equation.

`construct_pending_phase` follows the complete source probe schedule. It
derives exactly one of three possible pending callback phases:

- The original Depth callback reports pending.
- The original Depth callback returns. The selected ordinary callback reports
  pending from the actual returned Depth cache.
- Both probes return. Their actual returned cache has complete coverage.
  The final key is absent. The source reserves that key, and its fresh body
  callback reports pending from the actual allocated cache.

`maybeMu_pending_phase` also derives that the pair name is actually free in
the original body. `NativeConstructorPhase.constructor_trace_phase` connects
these phases to an actual blocked native run and its derived pre-call coverage.
This covers arbitrary nested bodies. It does not assume prepared callbacks.

## Full repaired nested encounter and old probe records

`InternedFreshOrdinaryEncounter.build_encounter` follows any actual pending
repaired build. Its scope invariant retains actual ancestor reservations and
their captured fresh inputs. The mutual proof covers all source expressions,
members, and edges, including discarded effects. It derives an encountered
nested callback whose two normalized probes completed before the missing read.
The ordinary probe uses `ordinaryLevel depth`.

`Encounter` retains the actual callback syntax, captured environment, source
start, both completed probe equations, complete available probe records, and
the exact pending key. The current environment contains the pending ancestor's
fresh interned reference. Its `Origin` records the genuine earlier miss and
the two original available probes. These fields are derived from actual
execution and cache facts. They are not supplied probe-equivalence premises.

`InternedFreshOrdinaryOldCall.encounter_old` identifies both encountered probe
records with those original records through complete canonical readback.
It retains the earlier source cut, actual cache growth, fresh captured name,
and exact repaired callback equations. Both probes were available before
that fresh name was reserved. `old_probe_boundaries` excludes every boundary
at or above that cut's issued counter from their original boundary lists.
`closed_old_call` starts directly from an actual stopped repaired empty-cache
build. No source mismatch or origin witness is supplied.

`SourceRecursiveIntersectionMaybeMuEncounter.pending_encounter` connects an
actual optional-binder pending result to this full repaired encounter. It uses
the proved stored-body lexical equation, source facts, available original body,
and complete incoming coverage. Its captures come from the actual stored
body's leaves. It assumes no callback execution or termination contract.

## Preparation is not preserved at all native sites

`InternedStoredPreparationCheck.check_eq_true` proves a finite Boolean test
equivalent to `PreparedWithoutMu`. A closed value passes without inspecting
its payload. An open Mu fails. Open nodes and unions check their actual children.

`SourceRecursiveIntersectionOpenBodyBoundary` builds both inputs through the
actual repaired source executor from empty caches. Each input has the form
`mu x. node 0 c [mu y. node 1 c [x, y]]`, for `c = 1` and `c = 2`.
Both roots are closed, available, and original. The shared source heap has
complete payload coverage and the full repaired semantic context.

An actual 22-step native prefix reaches an optional binder with pair `(10, 26)`.
Its body has free names `[intersection 10 26]` and fails the finite test.
`not_all_closed_original_prepared` refutes preparation preservation even with
the full initial semantic context and a checked root key. It does not assert
word ranges on every later prefix. `native_returned` separately verifies
that bounded native execution returns the original right root. The example
refutes a proposed proof invariant. It does not show an implementation defect.
All observations use kernel reduction, not native evaluation axioms.

General native completion therefore needs a broader open nested constructor
invariant. Do not make preparation preservation the next proof target.

## Full active paths with arbitrary captured values

`InternedFreshOrdinaryActiveOrigins` retains an actual active reservation,
its raw Depth build, both repaired normalized probes, and the complete semantic
contexts. Its `Path` records every actual descendant callback crossing.
The captured environment can contain available records, not only references.

`InternedFreshOrdinaryActiveEncounter.complete_encounter` derives this witness
from actual pending execution, a semantic context, and complete coverage.
The mutual proof follows members, edges, and children in source order.
`InternedFreshOrdinaryActiveSite.encounter_site` uses canonical readback to
identify both complete current probe records with the original records.
It requires no supplied path, callback replay, or probe equality.

`Site.inputs` recovers the exact crossed-reference prefix before the original
captured values. `Site.capture_equivalent` derives equal captured free-name
memberships from the actual two probes. `Site.capture_below` puts every live
interned capture below the ancestor's reservation counter.
`Site.fresh_not_captured` excludes the ancestor's fresh name from this set.

`SourceRecursiveIntersectionMaybeMu.active_pending_site` connects an actual
pending optional binder to this full witness. It uses the body's available
leaves, complete incoming coverage, and an incoming repaired semantic context.
General preservation of that semantic context on native prefixes remains open.

## Earlier completed routes and actual different request pairs

`InternedFreshOrdinaryCompletedSites` extracts actual completed child calls
from ordered members and edges. Each call retains its original full semantic
context and the cache histories before and after that call.

`InternedFreshOrdinaryProbeChoiceSites.completed_route` follows both actual
probes at every binder in a completed enclosing run. Its crossing records
retain the actual Depth callback that selects `ordinaryLevel`. Captured
environments can contain arbitrary available records. It reuses only the pure
`Route` syntax from the older proof, not the older executor or ordinary choice.

`InternedFreshOrdinaryActiveReplay.Origin.completed_representative` starts
from the active origin's actual completed raw Depth build. It derives a
completed representative of the current pending site's syntax before the
origin reservation. It retains ordinary choices and replaces fresh choices
with Depth. Each crossing keeps its actual body and computed ordinary level.
The original captured values remain unchanged after the lexical prefix.
`Site.crossed_fresh_not_captured` also excludes every actual crossed fresh
interned name from the current capture set.

`InternedFreshOrdinaryEarlierPair.request_record` proves that any completed
canonical request leaves a payload at its actual pair key. It needs no callback
termination or coherence premise. `Site.earlier_pair` derives the earlier
completed route, both actual repaired probes, its completed request, and the
payload retained at the origin cut. At least one earlier probe reference
differs from the original ancestor probe reference. Otherwise that payload
would occupy the ancestor's missing key before its reservation.

## Exact live-input comparison with arbitrary fixed captured values

`InternedFreshOrdinaryLiveInputs` represents each lexical slot as a fixed
value or a varying reference. Both executions retain the same fixed records.
The symbolic profiles retain all fixed reference names. Free labels track
only varying slots. `callback_agreement` proves the exact local extension
through a binder. It does not assume equal computed ordinary levels.

`InternedFreshOrdinaryLexicalLiveness.buildMany_empty` derives the actual
empty-child test from those common symbolic profiles. The mutual proof in
`InternedFreshOrdinaryLiveInputReplay` compares actual completed expressions,
members, and edges. `build_same` proves equal complete returned records when
all surviving varying inputs agree. Both full semantic contexts and an actual
coherent common cache are required. Discarded source edges need no input
agreement. Their earlier computations can have different cache effects.

`InternedFreshOrdinaryLiveInputReadiness.not_pending_after_probes` needs an
earlier completed binder and the later actual completed probes. It derives
the later canonical request and excludes its pending readback. The later
binder is not assumed complete. Equal Depth records determine equal repaired
ordinary choices before the second callback comparison.

`InternedFreeNameInputSubset` proves free-name inclusion with fixed symbolic
profiles. `InternedFreshOrdinaryLiveInputSupport.callback_live` uses it to
expose each live varying capture in an actual callback's free-name list away
from its supplied argument. Names inside fixed captured records need not be
empty. Adding those names cannot remove the varying capture observation.

## Actual live ordinary mismatch

`InternedFreshOrdinaryRouteInputs` pairs the actual crossed references and
keeps the ancestor's complete captured values in a fixed tail. Both actual
environments are derived exactly. Every changed varying input is ordinary or
an interned name at or above the ancestor reservation counter.

`InternedFreshOrdinaryJointMismatch.Site.mismatch` starts from the actual
pending site and its derived earlier completed route. Agreement on all live
varying inputs would make that request complete. A changed live interned name
contradicts the original Depth probe's issued-name bound. The remaining
witness retains:

- The earlier completed source route, both probes, and completed request.
- Its different pair and retained payload before the ancestor reservation.
- One matched pair of actual source crossings with the same body.
- A live ordinary input with different earlier and current selected levels.
- The current level in the original ancestor Depth probe's free-name list.
- Its strict bound below the ancestor's selected `ordinaryLevel`.
- An actual earlier captured value that contains that ordinary name.

`closed_mismatch` derives this witness from actual repaired pending execution
in empty caches. `SourceRecursiveIntersectionMaybeMu.active_pending_mismatch`
derives it from the actual optional-binder call with incoming full semantic
context, body availability, and complete coverage. No route, callback replay,
probe equality, or ordinary mismatch is supplied.

## Rooted capture histories and actual shorter producers

`InternedFreshOrdinaryActiveEncounter.AtOrigin` and
`InternedFreshOrdinaryActiveSite.encounter_site_at` keep a specified origin
through canonical probe readback. The previous public encounter and site
statements remain. They use the same source equations.

`InternedFreshOrdinarySourceHistory.Reached` retains the path from the original
source call and growth from every crossed callback start to the current cache.
`Path.crossing_shorter` proves the strict captured-prefix bound.
`Path.crossing_tail` retains the descendant path from a selected callback.

`ProducedAt` contains an actual earlier producer body, captured values, source
context, completed Depth callback, selected `ordinaryLevel`, and cache history.
It also retains the path from the producer's ordinary body entry to the active
binder. `Path.inputs` gives the exact captured suffix relation. The producer's
captured prefix is strictly shorter than the active ancestor's captured prefix.

`InternedFreshOrdinaryRootScope` retains this original path for every active
reservation. `InternedFreshOrdinaryRootEncounter.complete_mismatch` follows
actual repaired pending execution through members, edges, and callbacks.
It derives the original path and the earlier joint mismatch at the same origin.
`closed_mismatch_producers` excludes initial captures from empty source inputs.
Every ordinary name in the original ancestor Depth probe has a `ProducedAt`
witness. No source path or producer is supplied.

`InternedStoredLeavesOrdinary.leaves_ordinary` proves that an ordinary name in
an available substitution leaf is free in the original stored body. It uses
coherent cached free-name fields and actual child availability. An interned
Mu binder cannot remove that ordinary name.

`SourceRecursiveIntersectionMaybeMu.rooted_pending_mismatch` derives the exact
original lexical plan and rooted mismatch from actual source execution.
`pending_capture_history` gives an initial-body free name or a `ProducedAt`
witness for every old ordinary capture. `pending_mismatch_producers` excludes
the initial alternative when the original body has no ordinary free names.
The body condition remains explicit. It is not yet derived at all native sites.
Incoming full semantic context, body availability, and complete coverage also
remain explicit.

## The producer path does not transfer result liveness

`InternedFreshOrdinaryProducerPathBoundary` checks the repaired policy.
A nested raw binder reads its outer ordinary name. An empty sibling then
removes the enclosing edge. The nested complete record remains stored with
that capture, while the enclosing producer returns empty. The mixed-input
support is live at the target and empty at the producer body. All observations
use kernel reduction. This is a counterexample to a proof shortcut, not source
nontermination or an implementation defect.

## Next proof target and retained boundaries

Exclude the full repaired encounter for the intended constructor scope.
The difficult case has two exact old probe records even though the current
callback captures the ancestor's newly reserved reference. An earlier completed
route, different earlier pair, and live ordinary mismatch are now derived.
Use `InternedFreshOrdinaryJointMismatch.Mismatch`. Do not repeat the
mixed-input comparison or replace fixed captured values with literal lists.

The original path, capture alternative, and actual shorter producer are proved.
Use `RootEncounter.complete_mismatch`, `ProducedAt`, and the actual optional
binder history theorems. Do not repeat this extraction.

Construct another actual observation of the shorter producer's same body.
Retain the exact captured suffix, both normalized callbacks where required,
and chronological growth into the original cut. A completed producer Depth
callback is not a completed producer binder or request. `ProducedAt` also does
not assert that its whole ordinary callback has a particular pending outcome.
Derive those source observations from actual execution before using them.
Then derive a new mismatching producer pair or computed level and apply the
strict captured-prefix decrease. One shorter producer does not itself prove
recursive descent. See [the paired producer obligation](notes-pending-producer-descent.md).
Do not assume equal computed levels across executions. Do not treat a live
ordinary alias as impossible without checking both actual probes.

Do not infer independence of the original substitution memo key from absence
in normalized output. Smart construction can erase a dependency. The retained
normalized-erasure example remains relevant. Root profiles and free-name
agreement do not imply equality of complete stored probe records.
Do not reuse ordinary-choice-specific mismatch theorems for the old executor
without proving the repaired counterpart.

`PreparedWithoutMu` and complete coverage already give successful source
completion. Coverage is derived at native sites after actual completed source
construction. Preparation preservation is refuted above. Prove a broader
nested constructor invariant. A supplied no-pending callback contract does
not close the source obligation.

General successful native first-run completion, output preparation, and
physical `ProductReadback.members`/`.rejected` remain open. Preserve the exact
reference, solver-decided, and optimized Sized results. Preserve earlier
constructor/equality proofs and all marked drafts.

## Validation and diagnostics

Pinned Lean 4.34.1 passes 1,326 jobs and 42,195 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-repaired-root-history-20261014-audit.log`.
The live-mismatch audit passed 1,320 jobs and 42,130 checks.
The earlier-pair audit passed 1,311 jobs and 42,066 checks.
The active-path audit passed 1,307 jobs and 42,042 checks.
The preparation boundary audit passed 1,303 jobs and 41,982 checks.
The pending encounter audit passed 1,301 jobs and 41,703 checks.
The intermediate coverage audit passed 1,296 jobs and 41,685 checks.
The phase audit passed 1,298 jobs and 41,689 checks.
Explicit signature checks confirm the repaired executor and `ordinaryLevel`:
`/tmp/mcfta-repaired-encounter-signature.log`.

A temporary diagnostic completed one two-binder source example. Earlier paired
source setup variants did not finish within 15- and 20-second limits.
These old runs produced no native preparation result or pending counterexample.
Logs: `/tmp/mcfta-native-nested-one.log`,
`/tmp/mcfta-native-nested-bind.log`, and
`/tmp/mcfta-native-nested-pair.log`. All diagnostic workers have stopped.
No performance or termination claim follows from these limits. The later
kernel-reduced preparation example above supersedes their lack of results.

No Haskell source changed. Prior Nix and formatter checks remain the source
validation checkpoint. All proof, draft, fixture, stash, and worktree
preservation requirements remain. Everything remains local.
