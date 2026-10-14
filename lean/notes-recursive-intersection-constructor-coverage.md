# Actual native constructor coverage and repaired pending encounters

Proof checkpoints: `83d79a1d` and `f79d0417`.
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

## Next proof target and retained boundaries

Exclude the full repaired encounter for the intended constructor scope.
The difficult case has two exact old probe records even though the current
callback captures the ancestor's newly reserved reference. Derive an earlier
completed request at that source site, or another sufficient key-separation
argument. Keep both actual probe identities and the repaired ordinary choice.

Do not infer independence of the original substitution memo key from absence
in normalized output. Smart construction can erase a dependency. The retained
normalized-erasure example remains relevant. Root profiles and free-name
agreement do not imply equality of complete stored probe records.
Do not reuse ordinary-choice-specific mismatch theorems for the old executor
without proving the repaired counterpart.

`PreparedWithoutMu` and complete coverage already give successful source
completion. Coverage is now derived at native sites after actual completed
source construction. Preparation for all reached open nested bodies is still
unproved. Closed original roots do not alone establish it. A larger nested
constructor invariant may be needed. A supplied no-pending callback contract
does not close the source obligation.

General successful native first-run completion, output preparation, and
physical `ProductReadback.members`/`.rejected` remain open. Preserve the exact
reference, solver-decided, and optimized Sized results. Preserve earlier
constructor/equality proofs and all marked drafts.

## Validation and diagnostics

Pinned Lean 4.34.1 passes 1,301 jobs and 41,703 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-repaired-pending-encounter-20261014-audit.log`.
The intermediate coverage audit passed 1,296 jobs and 41,685 checks.
The phase audit passed 1,298 jobs and 41,689 checks.
Explicit signature checks confirm the repaired executor and `ordinaryLevel`:
`/tmp/mcfta-repaired-encounter-signature.log`.

A temporary diagnostic completed one two-binder source example. Paired
source setup variants did not finish within 15- and 20-second limits.
They produced no native preparation result and no pending counterexample.
Logs: `/tmp/mcfta-native-nested-one.log`,
`/tmp/mcfta-native-nested-bind.log`, and
`/tmp/mcfta-native-nested-pair.log`. All diagnostic workers have stopped.
No performance or termination claim follows from these limits.

No Haskell source changed. Prior Nix and formatter checks remain the source
validation checkpoint. All proof, draft, fixture, stash, and worktree
preservation requirements remain. Everything remains local.
