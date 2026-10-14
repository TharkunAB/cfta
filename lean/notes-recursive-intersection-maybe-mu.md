# Source recursive intersection binder effects

Proof checkpoint: `0bf65249`. Upstream: `f59c198d`, 2026-10-14.
Source: `Interned/Operations.hs:intersectOpen`, `maybeMu`, and
`Interned/Type.hs:createMuDontCleanup`, `substitutionPlan`.

## Full stored callback conversion

`InternedFreshOrdinaryPlanEquivalence` relates complete lexical plans.
Equivalent plans can use different slots for equal captured values.
They retain symbols, guards, constructor order, union order, and every
nested binder callback. `build_exact` proves identical repaired execution.
The equality includes pending keys and complete returned caches.

`InternedStoredSubstitutionRebind.encode_equivalent` derives this relation
from actual stored source plans. Local binders shadow external bindings.
Closed constants retain their exact original complete records. The proof
uses coherent source context lookup. It does not assume a callback law.
`rebind_build` proves that replacing one stored free name is identical to
binding that name through a local slot. It covers full nested syntax and
arbitrary current caches. This permits a current cache with an unfinished
outer reservation. The captured source body still requires availability
in a coherent source cache.

## Actual optional-binder execution

`SourceRecursiveIntersectionMaybeMu.callback` applies the stored substitution
executor to the actual body, then removes the callback's direct self reference
at a union root. `construct` runs the Depth probe, selects the repaired fresh
ordinary reference from that actual result, runs the ordinary probe, and
executes the actual canonical Mu request with smart cleanup. `maybeMu` returns
the literal body when the exact RecIntersect pair name is absent.

`callback_eq`, `construct_eq`, and `maybeMu_eq` derive exact equality with the
repaired lexical executor. They retain both probes, the chosen ordinary name,
hits, pending payload reads, fresh reservation, stored body, cleanup, and the
entire outcome cache. No completed output or key equation is supplied.
`verified` derives source facts, physical growth, issued-map extension, and
complete availability of a returned value. `replay` retains the exact result
without allocation after later cache growth.

## Finite callbacks and the pending key

For `PreparedWithoutMu` bodies, `callback_complete` derives finite actual
normalized callbacks at every current cache. Closed nested Mu values can
remain opaque captures. The prepared traversal has no dynamic open Mu request.
The proof does not require whole-cache coverage.

`probes_complete` derives both actual probe results, their exact intermediate
caches, and the next source request. `pending_exact` then identifies the only
possible pending result: the post-probe Mu key is already installed, but its
complete payload is absent. The reported key is exactly that key. The returned
cache is exactly the post-probe cache. A miss executes its fresh body callback
and completes. No body callback in this prepared fragment reports pending.

`complete` derives finite successful first-run execution when the current
cache additionally has complete payload coverage. It returns the actual final
facts, available result, physical growth, and issued history. The coverage and
prepared-body premises remain explicit. These proofs do not establish general
open nested completion or preparation of every newly stored Mu body.

## Later full nested coverage and pending encounters

The later [constructor coverage](notes-recursive-intersection-constructor-coverage.md)
proofs cover arbitrary repaired nested syntax. Completed actual callbacks
and optional binders retain payload coverage without preparation. Every
actual native yielded prefix retains incoming coverage. Bounded constructor
blocks derive their original source site and complete pre-call coverage after
actual completed source construction.

Exact pending-phase extraction excludes an incomplete final hit after two
successful probes. Full repaired pending encounters recover the earlier
ancestor reservation and both original available probe records. The repaired
ordinary callback uses `ordinaryLevel depth`. `pending_encounter` connects
actual stored-body source execution to that witness. Earlier completed-request
replay or key separation for the joint old-probe alias remains open.

## Remaining recursive caller obligations

These source binder effects and the physical branch/domain proofs now compose
in the uncached recursive caller at `95792559`. Its complete cache invariants,
stable bounds, and literal guarded row readback are checked. Read
[recursive caller](notes-recursive-intersection-kernel.md) and
[recursive control](notes-recursive-intersection-control.md).
Retain recursive node and edge memo requests, child effects, canonical domain
identities, ordered operands, union requests, and conjoined guards. Derive the
result's product language and the actual product-row membership and rejection
conditions. Do not supply equivalent product-language premises.

General open nested calls still need a complete-key separation argument or
another finite-execution invariant. A general recursive result also needs
derived preparation or a larger cold-exposure invariant. The native lazy
memo publication and thunk-forcing behavior remain separate. The stored
executor is a handwritten source model; these equalities do not establish
verified Haskell extraction.

## Validation

All three modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
aggregate build passes 1,212 jobs and 40,366 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-recursive-maybe-mu-20261014-audit.log`.
No Haskell source changed. The prior passing Nix and formatter checks remain
the source validation checkpoint.
