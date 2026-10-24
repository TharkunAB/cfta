# Pure cached selection and canonical waiting counts

Source review at 2026-10-24 01:33 CEST. HEAD was verified as `65f237954c3e867570c06d2de22681f55ca64fcd`. The current Enumeration.hs SHA256 remains `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07`. No native source bug was identified. The existing raw waiting model is not the current source cache representation.

The complete relevant Haskell functions were read: initialization; allocation; representative lookup; raw setters; gained/lost writes; value assimilation; node merging; terminal-class unions and count transfer; shallow-child installation; and both selection functions. The existing Lean waiting, expandable, indexed-selection, and machine-counter interfaces were compared. Eight full-file identities and 18 exact cut identities are in `/tmp/mcfta-cached-selection-20261024-source-inputs.json`, SHA256 `52878c8fd473e0d2956e9aa7c1d773e35589b2485af40461599a987a2ca3c519`. That JSON retains byte counts and full SHA256 values for every input and cut. This is a bounded source review, not a claim to have read every proof in the import closure.

## Current selector

`Enumeration.hs:827-834` reads the actual expandable IntSet and the waiting IntMap. If the candidate set is empty it returns Nothing. Otherwise it returns Just of candidate IDs minus the stored waiting keys. It does not resolve keys, scan suspended references, write the state, consume fuel, or compress representatives. A present zero-valued map entry would still block its key; the executable selector must test map presence, not positivity. Correct source histories derive positive stored counts separately.

`nextExpandableUVar:855-870` distinguishes Nothing from Just empty, offers the remaining IDs in ascending order, accepts a preference only if it is a member, and otherwise chooses the minimum. The offered IDs remain raw slot IDs. They are not mapped through representatives or deduplicated again. Quiescent slot invariants make each offered live slot a representative; this fact is not implemented by the selector itself.

The smallest additive executable proposal reuses the existing `EnumerationExpandableIndex.Cached` carrier:

```
findCached state :=
  let candidates := EnumerationIndexSelection.candidates state
  if candidates.isEmpty then none
  else some (candidates.filter fun uv => (state.waiting uv).isNone)

nextCached preference state :=
  EnumerationState.pickNext preference (findCached state)
```

These are pure functions. A state-action wrapper, if needed, returns exactly one successful row containing the original complete state. There is no representative-fuel parameter, raw waiting-key list, key resolver, or call to `findIndexed`. Reuse the existing aligned slot-domain and expandable-membership fields to connect `candidates` to the source IntSet.

## Counterexample to reusing the old raw invariant

`EnumerationWaitingIndex.Correct` counts occurrences of literal `sc.var`. Current source `writeUVarValue:450-466` counts `UnionFind.root sc.var` instead. Consider three slots, a representative map with 1 pointing to root 0, and candidate slots 0 and 2. Slot 1 is eliminated. Slot 2 contains one suspended reference with raw variable 1. Slot 0 contains no suspended reference.

The source waiting table stores `0 -> 1`, so pure cached selection offers only `[2]`. The old raw invariant instead stores `1 -> 1`. Subtracting those raw keys directly would wrongly offer `[0,2]`. The old `findIndexed` resolves raw key 1 to 0 and returns the correct offered list, but executes representative lookups. It is therefore a different model, not the current pure scheduler. This example is source-derived; no test or compiler was run for it.

`EnumerationIndexSelection.selection_exact` proves equal offered results and common canonical Roots, not identical final forests. A deeper alias chain can be compressed by the old scan while the pure source selector leaves it intact. The new selector-to-old-scan statement must preserve every non-representative field, including both ancestry fields, and relate representative meanings. It must not assert literal forest equality.

## Canonical count view

Root's accepted minimal schema reuses the raw count theorems through `canonicalValue roots`. That function changes only suspended `sc.var` to `roots sc.var` in unenumerated values. It retains nodes, tries, list order and multiplicity, enumerated fragments, and eliminated slots. It is a ghost count view. It must never replace the executed value slots or rendered hole IDs.

```
CanonicalCorrect roots values waiting :=
  EnumerationWaitingIndex.Correct
    (values.map (canonicalValue roots)) waiting
```

The existing `Correct` field on `Cached` cannot be reused as the source invariant. Use the new canonical count predicate, the existing expandable/alignment equations, and an explicit `Roots core.representatives roots` realization. The executable selector does not use or compute `roots`.

The exact key-support consequence is:

```
waiting key != none iff
  exists value in values, sc in references value, roots sc.var = key
```

No root-fixed premise is needed for this count algebra. Tying the map to a real union-find forest is a separate step. Under that tie, idempotence of canonical representatives derives that every stored key is a root. Candidate invariance follows because `canonicalValue` preserves suspended-list emptiness.

## Actual maintenance boundaries

- Initialization has no references. Allocation appends an empty suspended list, sets the exact candidate flag, and inherits ancestry. Neither operation adds a waiting count.
- General replacement removes every old reference before adding every new reference. Both folds use the same current representative map through pure `UnionFind.root`. With a fixed class map, reuse raw replacement correctness on the canonical count view and `List.map_set`.
- `mergeNodeIntoUVarVal:516-525` retains all old constraints and adds the new list. Its literal gained/lost parameters are new `scs` and empty. Shallow-child installation allocates an empty list and then uses ordinary full replacement to install its complete inherited list.
- Narrowed-node replacement with unchanged `scs` removes and re-adds the same class occurrences. Clearing repeated-recursion constraints and storing an enumerated fragment remove the old list. Candidate membership must be updated at the written raw slot in each case.
- Representative path compression preserves class meanings. It can frame the canonical invariant only under that preserved-map fact. The older `ExpandableIndex.frame_correct`, which permits arbitrary forest replacement when slots/counter match, is not by itself a canonical-count preservation theorem.
- Terminal merging captures the old representatives before unions (`733`), performs the unions, resolves the actual final root, deduplicates the old representatives, removes that final root from the transfer set, and moves each other stored counter into the final root (`739-743`). References inside value slots can remain aliases. They must not be renamed in the actual heap.
- Assimilation uses two empty-delta writes (`506-507`): store the combined contents in the target and eliminate the source. Their complete pair preserves reference multiplicity by moving the source list rather than adding a second copy. The first write alone temporarily duplicates the source list in the raw slots. Do not require the full count invariant after that first write.

The canonical invariant is a quiescent invariant. It can fail temporarily after a forest-only union, before its waiting-key transfer, and between the two assimilation writes. Prove the union-and-transfer and assimilation pairs as completed transactions. A transfer-fold proof can use ghost partial redirect maps; those maps need not equal the already-final native forest at each internal fold step. No new operational state machine is required for that algebra.

## Minimal bucket transfer and handoff

For arbitrary class maps, define `redirect target source roots uv` as `if roots uv = source then target else roots uv`. The literal transfer has a target-equals-source identity guard. Otherwise a missing source key leaves the table unchanged. A present source count deletes that key and stores `some (sourceCount + oldTarget.getD 0)` at the target. Do not encode/delete zero in this executable move. Correctness derives that the stored sum is positive.

This supports a map-only move theorem without root-fixed premises. The real union-find realization later proves that actual old representatives and final target have the corresponding redirected class map. The source's deduplicated old-root set is essential for that realization. A list fold of transfers matches a ghost list fold of redirects; a repeated or target entry is harmless in this algebra but is not a claim that the source loops over duplicates.

Root authorized a separate uncompiled candidate, `/tmp/mcfta-cached-selection-20261024-canonical-waiting.lean`, 239 ordinary lines, SHA256 `fcb7c910fb67bf253bfb7c6b5ed9d1bb1f5e186cb78cf18f52e7a9cbe7dbdd70`. It includes the count view, fixed-map replacement/allocation/initial support, and arbitrary-map transfer/fold proof candidates. Root owns compilation and theorem selection. It claims no complete native State/forest maintenance result.

Machine Int bounds remain separate. Alias classes aggregate counts that were formerly in different raw buckets. Bounds must cover these canonical sums and all intermediate transfer additions, not merely each old raw bucket. Existing `EnumerationWaitingMachine` integer/word lemmas provide prior arithmetic, but their raw-view bounds do not automatically establish the new canonical aggregate bound.

No repository source was changed by this reviewer. No compiler, Lean proof check, selected program, Git mutation, network operation, or board operation was run. The later `/tmp` proof candidate is explicitly uncompiled. All existing raw-cache definitions and theorems remain unchanged and retain their actual older-model scope.
