# Stored free-name support and general single unfolding

Updated: 2026-10-14 12:18 CEST. Proof checkpoint: `2ac3ca41`.

## Exact used lexical positions

`InternedFreeNameIndexedOrigins.Uses` records an external lexical occurrence
through the complete syntax. Binders shift the external position. The
relation can include a child in a deleted edge. `evaluate_indexed` proves
that each returned pure free name comes from a used position. `source_indexed`
derives the exact position, original captured record, and free membership
from actual repaired source execution.

`InternedStoredPlanFreeSupport.encode_free` connects a used captured slot to
the original available stored value. Canonical slot lookup supplies the
complete record. A name at that slot is free in the original value and absent
from every enclosing local binder. The proof includes arbitrary nested Mu,
union, and node records and closed captures.

## Actual optional-binder support

`SourceRecursiveIntersectionMaybeMuFreeSupport.free_support` follows the
actual stored-body compilation and repaired source return. Every returned
free name was free in the original body. It differs from the selected
intersection name. `pair_absent` states that elimination directly.
Normalization can remove additional names, so no exact set difference is
claimed. These theorems require the actual completed result and a coherent
semantic context. They require no preparation or source termination premise.
Checkpoint: `018f1712`.

## General repaired stored substitution

`InternedStoredLeafShape` proves that every source leaf is a closed capture
or one literal reference. `InternedFreshOrdinaryStoredFreeSupport.free_support`
proves that every result free name comes from the actual replacement of an
original free reference. Closed captures contribute no free name. This
statement retains the actual optional replacement and its complete value.

`InternedFreshOrdinaryUnfoldCompletion.execute_complete_decoded` applies
general repaired source completion to the actual encoded stored plan and
available replacement inputs. It derives successful execution, exact final
cache, retained lexical context and all semantic heaps, complete coverage,
result availability, physical growth, and issued history.

`unfold_complete_decoded` derives the same result for one actual Mu unfolding.
`unfold_closed` proves that an actual unfolding of a closed available record
is closed. The original Mu free field excludes its own bound name. Every
other body free name is therefore absent. The replacement of the bound name
is the original closed Mu, which contributes no free name.

## Next obligations

Use the optional-binder support law to derive a recursive caller invariant:
each result free name is an intersection reference from the incoming domain's
`seen` pairs. A Mu body call adds its current pair. Its actual optional binder
removes that pair. Ordinary rows and unions retain only returned child names.
The empty initial domain should then derive native output closedness through
the existing guarded kernel meaning. This invariant remains to be proved.

General single unfolding does not prove termination of repeated cold-reader
traversal. It can add Mu records. The old `NoNewMu` inventory budget applies
only to prepared caches. Use the actual repaired reader in
`MergedFreshOrdinaryExposure` for a broader invariant. Do not silently use
`MergedSourceExposure`, whose general executor retains the old probe policy.
Its prepared equality bridge remains valid. A finite final cold table and
physical `ProductReadback.members` and `.rejected` remain open.

## Validation

Lean 4.34.1 passes 1,354 aggregate jobs and 42,506 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-unfold-completion-20261014-audit.log`.
No Haskell source changed. The prior Nix and active package formatter checks
remain the source validation checkpoint.
