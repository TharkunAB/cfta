# Immediate parked suffix: module boundary

Status: read-only source audit. No standalone proof candidate is selected. No compiler was run.

The exact statement cannot use only modules below `SourcePruningEnumerationSharedEagerReservation`. Its `reserved` premise uses `SourcePruningEnumerationSharedEagerReservation.eagerReserved`. That public predicate is declared only in the owner at line 307. It refers to the private `nodeReserved` family at lines 278–304 and to `eagerFinal` at line 85. Thus the original statement already requires the owner. Replacing this premise by an independent predicate would change the frozen statement.

The current proof also uses owner-private `nodeReserved_fallback` at line 1061 and `real_eager_held_fragment_history_at_every_depth` at line 25698. An ordinary import cannot name those private declarations. The private fallback theorem extracts the actual lower-depth reservation. The private held history provides both protected-held classes and the origin receipt used by `expanded_birth_kept_dependencies`.

The public held theorem at line 25775 exposes isolation, protection and pending-target avoidance. It does not expose the full origin receipt. The public Kept theorem at line 29116 exposes dependency closure directly, so an alternative proof could reuse that projection and avoid the private held theorem. This does not remove the statement dependency on owner-defined `eagerReserved`, or establish an owner-free module.

## Existing public boundaries

- `SourcePruningEnumerationParkedRemovedBucketInputs.actual_parked_removed_bucket_inputs` at line 26 retains the actual original bucket, immediate post-clear input facts, isolation and literal REAL restart. Its module is below the owner.
- `SourcePruningEnumerationSharedRecursive.prefix_real_continuing_current_at_original_budget` in `SourcePruningEnumerationRealPrefixContinuingResources`, line 504, gives the actual current Packet, Fits and Heap facts. Its module is below the owner.
- `SourcePruningEnumerationSharedRecursive.prefix_real_phase_admission_at_original_budget` in `SourcePruningEnumerationObservedRealPrefixAdmission`, line 212, gives actual mass admission. Its module is below the owner.
- `EnumerationDependencies.expanded_birth_kept_inputs` and `expanded_birth_kept_dependencies` in `EnumerationExpandedBirthKeptSet`, lines 43 and 16, are public algebraic receipts below the owner.
- `runEager_real_expanded_birth_history_at_any_budget`, `runEager_real_pending_bucket_kept_at_any_budget`, and `runEager_real_pending_target_fragments_avoid_isolated_at_any_budget` are public, but all three are declared in the resource owner.

The normal lower imports for the clear, current-state, mass and Kept parts are:

```
MicroCFTA.SourcePruningEnumerationParkedRemovedBucketInputs
MicroCFTA.SourcePruningEnumerationRealPrefixContinuingResources
MicroCFTA.SourcePruningEnumerationObservedRealPrefixAdmission
MicroCFTA.EnumerationExpandedBirthKeptSet
```

These imports do not define the original reservation predicate or the all-depth history theorems. Adding an import of the owner would resolve the public declarations but violate the requested owner-free boundary. It would not expose private declarations to the current proof.

## Selected boundary

Keep the frozen immediate-suffix producer as an owner-local proof pending its strict check. If publication is wanted, its theorem can be made public at the same owner boundary. A later consumer can import that boundary normally. This audit does not create a wrapper, change visibility, move definitions, duplicate the worker, or add a new reservation premise. An owner-free extraction would require a separate decision to move the existing reservation/history boundary and its dependencies. That is outside this bounded task.

The copied reference header is byte-exact with the original private header. This audit adds no theorem and gives no logical proof credit. It does not establish a compatible assignment for all removed historical obligations.
