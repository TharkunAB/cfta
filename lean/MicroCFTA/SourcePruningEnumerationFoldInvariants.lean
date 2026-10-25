import MicroCFTA.SourcePruningEnumerationFold
import MicroCFTA.SourcePruningEnumerationDispatchShape
import MicroCFTA.EnumerationCanonicalWaiting

namespace MicroCFTA.SourcePruningEnumerationFoldInvariants
open EnumerationState EnumerationCorrectness
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-!
# Storage and waiting counts through the checked fold

Each returned outer state retains storage validity and the fixed waiting counts.
The dispatcher action runs at the state from which it captured its references.
-/

/-- Concatenated pending references retain storage and canonical waiting counts. -/
theorem assimilated_preserves
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat)
    (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (roots : Nat → Nat) (waiting : EnumerationWaitingIndex.Waiting)
    (storage : StorageValid before)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (different : target ≠ source) :
    StorageValid (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) ∧
      EnumerationCanonicalWaiting.Correct roots
        (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values waiting
 := by
  have sourceBound : SlotBound before.counter (.unenumerated sourceNode sourceScs : UVarValue Symbol) := by
    exact storage.values _ (List.mem_of_getElem? sourceStored)
  have targetBound : SlotBound before.counter (.unenumerated targetNode targetScs : UVarValue Symbol) := by
    exact storage.values _ (List.mem_of_getElem? targetStored)
  have mergedBound : SlotBound before.counter (.unenumerated merged (sourceScs ++ targetScs) : UVarValue Symbol) := by
    intro sc member
    rcases List.mem_append.mp member with sourceMember | targetMember
    · exact sourceBound sc sourceMember
    · exact targetBound sc targetMember
  have first : StorageValid {before with values := before.values.set target (.unenumerated merged (sourceScs ++ targetScs))} := by
    exact set_storage before storage target (.unenumerated merged (sourceScs ++ targetScs)) mergedBound
  have second : StorageValid {{before with values := before.values.set target (.unenumerated merged (sourceScs ++ targetScs))} with
      values := (before.values.set target (.unenumerated merged (sourceScs ++ targetScs))).set source .eliminated} := by
    exact set_storage _ first source .eliminated trivial
  exact ⟨⟨second.aligned, second.total, second.forest, second.values, second.guards⟩,
    EnumerationCanonicalWaiting.assimilation_correct roots before.values target source
      (.unenumerated sourceNode sourceScs) (.unenumerated targetNode targetScs)
      (.unenumerated merged (sourceScs ++ targetScs)) different sourceStored targetStored rfl waiting counts⟩

/-- A selected successful singleton retains storage and waiting counts. -/
theorem dispatch_preserves
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (roots : Nat → Nat) (waiting : EnumerationWaitingIndex.Waiting)
    (storage : StorageValid before)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (selected : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    StorageValid after ∧ EnumerationCanonicalWaiting.Correct roots after.values waiting
 := by
  rcases SourcePruningEnumerationDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact ⟨storage, counts⟩
  · exact assimilated_preserves before source target sourceNode targetNode merged sourceScs targetScs
      roots waiting storage counts sourceStored targetStored (Ne.symm different)

/-- Every returned outer fold state retains storage and waiting counts. -/
theorem run_preserves
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (roots : Nat → Nat) (waiting : EnumerationWaitingIndex.Waiting)
    (storage : StorageValid before)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (observed : SourcePruningEnumerationFold.run checkEmpty nativeFuel p h sources
      beforeCaller before target queries = (result, afterCaller, savedQueries, after)) :
    StorageValid after ∧ EnumerationCanonicalWaiting.Correct roots after.values waiting
 := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
    simp only [SourcePruningEnumerationFold.run, Prod.mk.injEq] at observed
    rcases observed with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨storage, counts⟩
  | cons source rest ih =>
    rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
    cases dispatchResult with
    | error fault =>
      simp only [SourcePruningEnumerationFold.run, dispatchObserved, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨storage, counts⟩
    | ok possible =>
      cases possible with
      | none =>
        simp only [SourcePruningEnumerationFold.run, dispatchObserved, Prod.mk.injEq] at observed
        rcases observed with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨storage, counts⟩
      | some action =>
        cases rawObserved : ExceptT.run (action before) with
        | nil =>
          simp only [SourcePruningEnumerationFold.run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨storage, counts⟩
        | cons head tail =>
          cases head with
          | error error =>
            simp only [SourcePruningEnumerationFold.run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
            rcases observed with ⟨rfl, rfl, rfl, rfl⟩
            exact ⟨storage, counts⟩
          | ok pair =>
            rcases pair with ⟨valueUnit, middle⟩
            cases valueUnit
            cases tail with
            | nil =>
              obtain ⟨middleStorage, middleCounts⟩ := dispatch_preserves checkEmpty nativeFuel p h
                beforeCaller before source target queries action reachedCaller saved middle roots waiting
                storage counts dispatchObserved rawObserved
              simp only [SourcePruningEnumerationFold.run, dispatchObserved, rawObserved] at observed
              exact ih reachedCaller middle saved middleStorage middleCounts observed
            | cons second remaining =>
              simp only [SourcePruningEnumerationFold.run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨storage, counts⟩

end MicroCFTA.SourcePruningEnumerationFoldInvariants
