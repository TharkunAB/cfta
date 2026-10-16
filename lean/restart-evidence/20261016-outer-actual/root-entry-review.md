# Root caller initialization review

Reviewed at 2026-10-16 14:48 CEST. This is a read-only source audit and a proposed proof step. No Lean build, test, Haskell run, or Git mutation was performed.

## Result

The existing construction and allocation proofs can derive a cold logical root caller's full `PartialInvariant.Context` and its allocated empty inherited equality value. The next theorem should package those proofs. It need not ask callers for separate `Good`, semantic heap, field loads, input-model validity, cache coverage, or probe facts.

This package would remove the initialization premises of `SourceCurrentAllocatedPartialWorkerActual.root_exact` at `lean/MicroCFTA/SourceCurrentAllocatedPartialWorkerActual.lean:484`. It would retain that endpoint's reached range plan and literal successful execution. It would not establish general outer progress or the concrete process-global cache initialization adapter.

## Exact source entry

- `cfta/src/Data/CFTA/Equality/Operations.hs:68` defines `reducePartially = reducePartially' EmptyConstraints`. The root inherited value is an equality value, not the full transition constraint `noConstraint`.
- `cfta/src/Data/CFTA/Equality/Constraint.hs:313` defines `EmptyConstraints = EqConstraints []`. The builder at line 273 calls `internEqConstraints`; lines 280–286 use the retained process-global equality interner. Equality at line 288 compares canonical identities.
- `cfta/src/Data/CFTA/Constraint.hs:203` defines `noConstraint = Constraint EmptyConstraints Top`. The default edge builder uses it at `cfta/src/Data/CFTA/Interned/Type.hs:537`. Root invocation alone does not establish that this compound value is forced.
- `cfta/src/Data/CFTA/Equality/Operations.hs:72` creates a process-global `TypeableMemoCache`. The root call uses it at line 80. The logical cold root below does not assert that a Haskell call resets it.

## Existing constructive parts

`SourceCurrentAllocatedNativeOriginalHistory.constructed` at `lean/MicroCFTA/SourceCurrentAllocatedNativeOriginalHistory.lean:126` takes one covered causal allocation `History`, valid initial equality cache, and an actual fresh original build. It derives checked `Good`, `SemanticReady`, root availability, empty free-name metadata, and `Original`. The returned operation state retains the exact history's final equality interner. `History.fields` at line 92 derives successful existing field loads in that same cache.

`SourceCurrentConjunctionClassHistoryEntry.constructed` at `lean/MicroCFTA/SourceCurrentConjunctionClassHistoryEntry.lean:32` adds the stored cost heap, empty native scope invariant, and native idle state. Its result is the current full `ClassScan.Ready`. The actual build also derives `ProbeHeap` through `SourceCurrentAllocatedMuRebuild.constructed` at `lean/MicroCFTA/SourceCurrentAllocatedMuRebuild.lean:23`.

The remaining empty inherited value has a direct allocation route:

1. Let `baseOps := SourceEqualityConstraintMemoAllocation.initial finalCache`.
2. Let `emptyPair := SourceEqualityConstraintAllocation.intern (some []) finalCache`.
3. Let `ops := SourceEqualityMkEdgeAllocation.emptyField baseOps`.

`intern` at `lean/MicroCFTA/SourceEqualityConstraintAllocation.lean:48` makes `emptyPair.1` definitionally `.live identity []` for the actual returned canonical identity. Do not fix that identity to zero. `emptyField_correct` at `lean/MicroCFTA/SourceEqualityMkEdgeAllocation.lean:80` derives operation validity, operation growth, and `Ready ops.constraints emptyPair.1`. An existing canonical entry is retained; a missing entry is allocated.

This use of `emptyField` reuses the exact empty-equality allocation implementation. It is a logical initialization prefix. It does not assert that the root source call executes the sentinel constructor from which the helper's name comes.

The heap and native state do not change. Update `Good.operations` using the allocation result and `Good.fields` using `SourceCurrentConjunctionEquality.Fields.grows` at `lean/MicroCFTA/SourceCurrentConjunctionEquality.lean:60`. Keep the already derived semantic, cost, scope, and idle facts. No universal guard-combination law or future field premise is needed.

## Full Context assembly

Use the literal checked initial native state with `ops`, then `PartialState.initial` with empty merge and fourth tables. The two caller result families are empty by `lean/MicroCFTA/SourceCurrentAllocatedPartialState.lean:60`.

| `PartialInvariant.Context` field | Existing derivation |
| --- | --- |
| `ready` | Covered construction plus the operation-only empty allocation growth above. |
| `admitted` | Compute the singleton inventory with source `heap` and roots `[value]`. Derive its `Facts` from the actual build, its `Original`/availability/closedness from construction, and apply `InventoryState.initial` at `lean/MicroCFTA/SourceCurrentAllocatedNativeInventoryState.lean:75` with reflexive source growth and issued history. `Inventory.inputs` at line 34 computes the model. |
| `sound` | `PartialMemoSound.initial_sound` at `lean/MicroCFTA/SourceCurrentAllocatedPartialMemoSound.lean:105`. Empty caller tables need no result law. |
| `stored` | `MemoMergeEffects.stored_empty` at `lean/MicroCFTA/SourceCurrentMemoMergeEffects.lean:27`. |
| `covered` | `MemoMergeLanguage.cache_covers_empty` at `lean/MicroCFTA/SourceCurrentMemoMergeLanguageContracts.lean:25`, for each ambient environment. |
| `correct` | `CurrentEmptinessMemo.empty_correct` at `lean/MicroCFTA/SourceCurrentEmptinessMemo.lean:43`. |
| `globals` | The literal bundle of empty unfolding and endpoint query tables. Use `InternedFreshOrdinaryUnfoldMemo.empty_correct` at line 31 and `SourceEndpointMemo.empty_valid` at line 47. `EndpointMemoGateTrace.Valid` is at `lean/MicroCFTA/EndpointMemoGateTrace.lean:31`. |
| `probes` | `AllocatedMuRebuild.constructed`, cited above. |

These are precisely the eight fields in `lean/MicroCFTA/SourceCurrentAllocatedPartialInvariant.lean:25`. Native caches, operation memo tables, caller result tables, merge table, fourth table, and global three-table bundle must stay separate in the statement.

## Minimal next theorem

Add one initialization module. A proposed `constructed_root` should take:

- `width`, formulas, and solver;
- an actual `History initialCache finalCache originals` and `Cache.Valid initialCache`;
- an original syntax expression and coverage of its literal guards by `originals`;
- the actual completed fresh build `build expression [] empty = .done value heap`.

Define `emptyPair`, `ops`, the literal checked initial state, the cold caller, and the empty global bundle as above. Return a computed singleton inventory and canonical `identity` with:

```text
emptyPair.1 = .live identity []
EqAllocation.Ready ops.constraints (.live identity [])
PartialInvariant.Context formulas solver inventory caller globals
Available heap value
value.free = []
Original value
```

This is a proposed API, not a compiled theorem. It is enough to invoke the current literal `root_exact` and retain its same-result, entire-caller, strict-read, `Checks`, full `Post`, availability, and all-ambient language equivalence conclusions. The root call must use the literal returned empty interner state, not `finalCache` before that allocation.

A second convenience wrapper can derive the `History` using `SourceEqualityOriginalAllocationPreparation.prepare_complete` at `lean/MicroCFTA/SourceEqualityOriginalAllocationPreparation.lean:85`. It takes normalized literal equality fields and valid starting cache, then retains the exact `prepare ...` result. `SourceCurrentAllocatedNativePreparedHistory.query_complete` at `lean/MicroCFTA/SourceCurrentAllocatedNativePreparedHistory.lean:25` already demonstrates that pattern. A cold equality-interner specialization can discharge initial validity with `Cache.empty_valid`. Neither wrapper proves that arbitrary source constructors normalize their inputs or that GHC executes a serial preparation pass.

## Boundaries to preserve

The proof would establish initialization for the completed modeled original construction domain. It would not cover arbitrary malformed values or an unproved frontend constructor history. The supplied-success root theorem would still require actual reached checks and an actual successful bounded worker return. General outer termination/progress is a separate obligation.

The modeled cold native and caller tables are a deliberate initial-state specialization. Actual source equality and Typeable caches can already be warm. Their initial state, canonical identity correspondence, lazy forcing, recursive publication, and shared CAF lifetime require a concrete host adapter or a causal warm history. The same applies to source-global merge, emptiness, and query tables. The empty-equality prefix proves no GHC evaluation-order or CAF transfer claim.

This does not change the full-library objective. SMT/IO and solver laws, concrete machine bounds, and the remaining `Sized`/API adapters retain their existing scope. No Haskell defect or repair was found in this audit. Any future Haskell repair must be recorded first in the root `FINDINGS.md` registry by its owner.

## Reviewed source hashes

```text
e15c43f3681aefaf0fce08d8ee8c579f537606a1002ae5361feeb0b8a8ff14d1  lean/MicroCFTA/SourceCurrentAllocatedNativeOriginalHistory.lean
5281ba7124f3c12c5919d4329b217a15b8612db61ebe4a7a291950e865d92a12  lean/MicroCFTA/SourceCurrentConjunctionClassHistoryEntry.lean
5365ae3e5a39760b9052aef795c9eb609fb726516960fc48f5ef55367e41236a  lean/MicroCFTA/SourceEqualityMkEdgeAllocation.lean
5162416df367a97e743e2a0d38601026bb15862dc4c648fa518ad0308a919bc0  lean/MicroCFTA/SourceCurrentAllocatedPartialInvariant.lean
2e3939ea0b0c27f7619f6366b34c193002c017877d50a84f6540dcd1d6ef1734  lean/MicroCFTA/SourceCurrentAllocatedPartialWorkerActual.lean
5bf6e9b0f4033c11ac7723a17fe8d1b94d95a259187f0402285ad0147e439b09  cfta/src/Data/CFTA/Equality/Operations.hs
9dd1a13bd4422a0778bee419679f34e45901ec1d38442a46781df84952537c48  cfta/src/Data/CFTA/Equality/Constraint.hs
dee73d12be74af16c54f1c6856a3a60b1c1ae612ad8a15d1665210e2c63641f3  cfta/src/Data/CFTA/Constraint.hs
```
