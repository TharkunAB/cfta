import MicroCFTA.SourceCurrentCachedPrepareObserved
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

/-! Actual incoming adaptation derives its exact waiting delta and successful-fuel uniqueness. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingAdaptObserved
open EnumerationState EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))

private theorem mapped_write (heap : Heap) (before : Cached) (read returned : Core) (after : Cached)
    (fuel target : Nat) (value : UVarValue Symbol) (incomingScs : List Suspended)
    (roots : Nat → Nat) (paths : Roots read.representatives roots)
    (observed : (SourcePruningEnumerationNativeIndex.write heap fuel target value incomingScs []
      (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame returned) = some after) :
    after.waiting = EnumerationCanonicalWaiting.count roots 1 incomingScs before.waiting ∧
      ∀ otherFuel other, (SourcePruningEnumerationNativeIndex.write heap otherFuel target value incomingScs []
        (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame returned) = some other →
        after = other := by
  obtain ⟨written, writeObserved, same⟩ := Option.map_eq_some_iff.mp observed
  have entryPaths : Roots (EnumerationExpandableIndex.frame read before).core.representatives roots := by
    simpa only [EnumerationExpandableIndex.frame] using paths
  refine ⟨?_, ?_⟩
  · rw [← same]
    change written.waiting = EnumerationCanonicalWaiting.count roots 1 incomingScs before.waiting
    have counted := SourceCurrentNativeCountObserved.write_waiting heap
      (EnumerationExpandableIndex.frame read before) written fuel target value incomingScs [] roots entryPaths writeObserved
    simpa only [EnumerationExpandableIndex.frame, EnumerationCanonicalWaiting.count, List.map_nil,
      EnumerationWaitingIndex.count, List.foldl_nil] using counted
  · intro otherFuel other otherObserved
    obtain ⟨otherWritten, otherWrite, otherSame⟩ := Option.map_eq_some_iff.mp otherObserved
    have equalWrites := SourceCurrentCachedPrepareObserved.write_some_unique heap
      (EnumerationExpandableIndex.frame read before) written otherWritten fuel otherFuel target value
      incomingScs [] roots entryPaths writeObserved otherWrite
    exact same.symm.trans ((congrArg (EnumerationExpandableIndex.frame returned) equalWrites).trans otherSame)

/-- Both literal raw branches add exactly the incoming references at any successful supplied fuel. -/
theorem adapt_observed (heap : Heap) (before : Cached) (read : Core) (raw : Raw)
    (fuel target : Nat) (incomingScs : List Suspended) (after : Cached)
    (roots : Nat → Nat) (paths : Roots read.representatives roots)
    (observed : SourcePruningEnumerationIncomingCacheAdapter.adapt heap fuel target incomingScs before read raw = some after) :
    after.waiting = EnumerationCanonicalWaiting.count roots 1 incomingScs before.waiting ∧
      ∀ otherFuel other,
        SourcePruningEnumerationIncomingCacheAdapter.adapt heap otherFuel target incomingScs before read raw = some other →
          after = other := by
  cases raw with
  | nil =>
      cases stored : read.values[target]? with
      | none => simp [SourcePruningEnumerationIncomingCacheAdapter.adapt, stored] at observed
      | some value =>
          cases value with
          | eliminated | enumerated => simp [SourcePruningEnumerationIncomingCacheAdapter.adapt, stored] at observed
          | unenumerated oldNode oldScs =>
              simp only [SourcePruningEnumerationIncomingCacheAdapter.adapt, stored] at observed
              have actual := mapped_write heap before read _ after fuel target _ incomingScs roots paths observed
              refine ⟨actual.1, ?_⟩
              intro otherFuel other otherObserved
              apply actual.2 otherFuel other
              simpa only [SourcePruningEnumerationIncomingCacheAdapter.adapt, stored] using otherObserved
  | cons first rest =>
      cases rest with
      | cons second tail => simp [SourcePruningEnumerationIncomingCacheAdapter.adapt] at observed
      | nil =>
          cases first with
          | error fault => simp [SourcePruningEnumerationIncomingCacheAdapter.adapt] at observed
          | ok result =>
              rcases result with ⟨⟨⟩, returned⟩
              cases stored : returned.values[target]? with
              | none => simp [SourcePruningEnumerationIncomingCacheAdapter.adapt, stored] at observed
              | some value =>
                  simp only [SourcePruningEnumerationIncomingCacheAdapter.adapt, stored, Option.bind_some] at observed
                  have actual := mapped_write heap before read _ after fuel target value incomingScs roots paths observed
                  refine ⟨actual.1, ?_⟩
                  intro otherFuel other otherObserved
                  apply actual.2 otherFuel other
                  simpa only [SourcePruningEnumerationIncomingCacheAdapter.adapt, stored, Option.bind_some] using otherObserved

end MicroCFTA.SourceCurrentIncomingAdaptObserved
