# Physical recursive intersection control

Proof checkpoint: `2a533cc5`. Upstream: `f59c198d`, 2026-10-14. Source:
`microcfta/src/Data/CFTA/Interned/Operations.hs:451` and
`microcfta/src/Data/CFTA/Interned/Type.hs:304`.

## Checked control and domain effects

`SourceRecursiveIntersectionControl.decision` reads the complete physical
payloads and their cached free sets. It retains source guard order: empty,
closed-domain reset, closed self, operand swap, repeated pair, Mu, union,
reference, and ordinary payload. Unresolved placeholders remain unsupported.
They do not become a missing bound-identity error. `self_record` recovers the
exact complete self result from canonical equality and coherent availability.
`repeated_unmemoized` retains the source RecIntersect memo bypass.

The source uses two orders. Constructor tags precede identity comparison in
operand order. IntersectId independently sorts the two identities.
`SourceRecursiveIntersectionSchedule.greater_encoded` connects actual physical
comparison to `IntersectSchedule.greater` through the complete memo-input
codec. It includes Mu, union, and RecInt operands. `swap_once` excludes another
swap of the reversed complete pair. `pair_encoded` connects the independently
sorted actual identities to the semantic schedule's pair.

`SourceRecursiveIntersectionDomain.extend` constructs ascending distinct map
and set keys. `extend_lookup_source` proves last-new-binding overwrite and
old-map fallback for typed source domains. Each source binding names its
original Mu at that Mu's own identity. This invariant is required. The proof
does not identify arbitrary malformed domains with source domains.
`lookup_mu` and `lookup_complete` recover the original complete physical Mu,
including its body and probes. Later constructor growth retains these records.
`intern_extended` uses the actual domain cache and its reserved empty identity.

`SourceRecursiveIntersectionEnvironment.bindings` reads the actual encountered
Mu operands in left-before-right order. `enter_correct` derives canonical key
order, typed complete bindings, domain-cache validity, and exact domain
allocation. `enter_overwrite` identifies the typed source overwrite semantics.
`enter_lookup` recovers each encountered complete original Mu.
`enter_schedule` connects actual operand identities and binding lists to the
semantic schedule's extended lookups. No binding-readback contract is supplied.

`SourceRecursiveIntersectionSchedule.decision_encoded` proves the complete
branch conversion. `SourceRecursiveIntersectionStep.run_selected` proves that
each selected branch gives the next computation of the existing semantic
executor. `physical_step` composes these results. It retains ordered union
requests, both Mu extensions, cutoff names, missing-binder errors, and ordinary
edge requests. The physical-to-view closedness equations remain explicit in
`physical_step`. The proof does not derive a complete physical semantic view.

## Next construction obligation

The next target is the physical source `maybeMu` call. Its callback performs
`substFree` on the actual recursive body at each selected reference. Connect
that callback to the repaired constructor while retaining the complete body,
both probes, the selected fresh ordinary reference, cleanup, cache hits,
reservations, and actual returned caches. Do not assume a completed binder.

Then retain outer recursive memo requests before these control branches.
Their keys keep the shifted domain identity and ordered operands. A swap
requests the reversed key. RecIntersect placeholders bypass this memo.
Completed ordinary memo provenance does not prove pending cyclic publication.

Derive `SourceCyclicRowsNativeGate.ProductReadback.members` and `.rejected`
from those actual executions. Do not supply another equivalent product-row
or language premise. Connect the result to `SourceColdSharedRows*` and the
completed Sized adapters. General open nested construction can require a
larger finite-execution invariant than `Prepared`. The current control and
domain proofs do not establish that invariant or full recursive construction.

## Validation

All five modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
aggregate build passes 1,209 jobs and 40,275 theorem dependency checks. It uses
only `propext`, `Classical.choice`, and `Quot.sound`.
Log: `/tmp/mcfta-recursive-control-20261014-audit.log`.
No Haskell source changed. The prior passing Nix and formatter checks remain
the source validation checkpoint.
