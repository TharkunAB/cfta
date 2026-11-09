import MicroCFTA.SourcePruningEnumerationSharedDispatchShape
import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
import MicroCFTA.SourcePruningEnumerationFoldInvariants
import MicroCFTA.EnumerationDependencies
import MicroCFTA.SourcePruningEnumerationNativeReferences

/-!
# State facts at actual shared fold returns

Only completed singleton actions change the outer state. Every other
outcome retains the state at that cut. Storage and waiting counts hold
at each returned state. The fold creates no enumerated slots.

The representative forest stays fixed. This fact does not imply that
LiveRoots holds after an arbitrary assimilation of two distinct roots.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedFoldState
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates
open EnumerationCompleteness (PendingAt)
open EnumerationReferences
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- The fold changes selected values and the target ancestry only. -/
structure Frame (before after : EnumerationState.State Symbol EnumGuard)
    (sources : List Nat) (target : Nat) : Prop where
  counter : after.counter = before.counter
  values_length : after.values.length = before.values.length
  representatives : after.representatives = before.representatives
  obligations : after.obligations = before.obligations
  expansion_ancestry : after.expansionAncestry = before.expansionAncestry
  recursion_ancestry : ∀ slot, slot ≠ target → after.recursionAncestry slot = before.recursionAncestry slot
  off_list : ∀ slot, slot ∉ sources → slot ≠ target → after.values[slot]? = before.values[slot]?
  origin : EnumeratedOrigin before after
  pending : PendingAt before target → PendingAt after target
  eliminated : ∀ (slot : Nat), before.values[slot]? = some UVarValue.eliminated →
    after.values[slot]? = some UVarValue.eliminated

private theorem frame_refl (before : EnumerationState.State Symbol EnumGuard)
    (sources : List Nat) (target : Nat) : Frame before before sources target :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    EnumeratedOrigin.refl before, id, fun _ => id⟩

private theorem frame_cons {before middle after : EnumerationState.State Symbol EnumGuard}
    {source target : Nat} {rest : List Nat}
    (first : Frame before middle [source] target) (second : Frame middle after rest target) :
    Frame before after (source :: rest) target := by
  refine ⟨second.counter.trans first.counter, second.values_length.trans first.values_length,
    second.representatives.trans first.representatives, second.obligations.trans first.obligations,
    second.expansion_ancestry.trans first.expansion_ancestry, ?_, ?_,
    first.origin.trans second.origin, fun pending => second.pending (first.pending pending),
    fun slot stored => second.eliminated slot (first.eliminated slot stored)⟩
  · intro slot different
    exact (second.recursion_ancestry slot different).trans (first.recursion_ancestry slot different)
  · intro slot outside different
    have outsideRest : slot ∉ rest := fun member => outside (List.mem_cons_of_mem _ member)
    have outsideHead : slot ∉ [source] := by
      intro member
      have same : slot = source := by simpa only [List.mem_singleton] using member
      exact outside (List.mem_cons.mpr (.inl same))
    exact (second.off_list slot outsideRest different).trans (first.off_list slot outsideHead different)

/-- A literal singleton has the exact value and ancestry frame of its selected source. -/
theorem dispatch_frame
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    Frame before after [source] target := by
  rcases SourcePruningEnumerationSharedDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact frame_refl _ _ _
  · have sourceInside := (List.getElem?_eq_some_iff.mp sourceStored).1
    have targetInside := (List.getElem?_eq_some_iff.mp targetStored).1
    have targetAfter :
        (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[target]? =
          some (.unenumerated merged (sourceScs ++ targetScs)) := by
      simp [assimilated, targetInside, different]
    have sourceAfter :
        (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))).values[source]? =
          some .eliminated := by
      simp [assimilated, sourceInside]
    refine ⟨rfl, by simp [assimilated], rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro slot outside
      simp only [assimilated, ite_eq_right outside]
    · intro slot outsideHead outsideTarget
      have outsideSource : slot ≠ source := by simpa only [List.mem_singleton] using outsideHead
      exact assimilation_frame before target source slot _ outsideTarget outsideSource
    · intro slot fragment stored
      by_cases atSource : slot = source
      · subst slot
        rw [sourceAfter] at stored
        cases stored
      by_cases atTarget : slot = target
      · subst slot
        rw [targetAfter] at stored
        cases stored
      rw [assimilation_frame before target source slot _ atTarget atSource] at stored
      exact stored
    · intro _pending
      exact (EnumerationCompleteness.assimilated_pending before target source merged
        (sourceScs ++ targetScs) (Ne.symm different) targetInside sourceInside).1
    · intro slot previous
      by_cases atSource : slot = source
      · subst slot
        exact sourceAfter
      by_cases atTarget : slot = target
      · subst slot
        rw [targetStored] at previous
        cases previous
      rw [assimilation_frame before target source slot _ atTarget atSource]
      exact previous

/-- A literal singleton preserves storage and the unchanged waiting index. -/
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
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    StorageValid after ∧ EnumerationCanonicalWaiting.Correct roots after.values waiting := by
  rcases SourcePruningEnumerationSharedDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact ⟨storage, counts⟩
  · exact SourcePruningEnumerationFoldInvariants.assimilated_preserves before source target
      sourceNode targetNode merged sourceScs targetScs roots waiting storage counts sourceStored targetStored
      (Ne.symm different)

/-- Every actual outcome retains storage, waiting counts and its completed-prefix frame. -/
theorem run_state
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol Constraint)
    (roots : Nat → Nat) (waiting : EnumerationWaitingIndex.Waiting)
    (storage : StorageValid before)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (observed : SourcePruningEnumerationSharedCachedTerminal.rawFold checkEmpty nativeFuel p h sources
      beforeCaller before target queries = (result, afterCaller, savedQueries, after)) :
    StorageValid after ∧ EnumerationCanonicalWaiting.Correct roots after.values waiting ∧
      Frame before after sources target := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
    simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, Prod.mk.injEq] at observed
    rcases observed with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨storage, counts, frame_refl _ _ _⟩
  | cons source rest ih =>
    rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
    cases dispatchResult with
    | error fault =>
      simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨storage, counts, frame_refl _ _ _⟩
    | ok possible =>
      cases possible with
      | none =>
        simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, Prod.mk.injEq] at observed
        rcases observed with ⟨rfl, rfl, rfl, rfl⟩
        exact ⟨storage, counts, frame_refl _ _ _⟩
      | some action =>
        cases rawObserved : ExceptT.run (action before) with
        | nil =>
          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨storage, counts, frame_refl _ _ _⟩
        | cons head tail =>
          cases head with
          | error error =>
            simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
            rcases observed with ⟨rfl, rfl, rfl, rfl⟩
            exact ⟨storage, counts, frame_refl _ _ _⟩
          | ok pair =>
            rcases pair with ⟨valueUnit, middle⟩
            cases valueUnit
            cases tail with
            | nil =>
              obtain ⟨middleStorage, middleCounts⟩ := dispatch_preserves checkEmpty nativeFuel p h
                beforeCaller before source target queries action reachedCaller saved middle roots waiting
                storage counts dispatchObserved rawObserved
              have headFrame := dispatch_frame checkEmpty nativeFuel p h
                beforeCaller before source target queries action reachedCaller saved middle dispatchObserved rawObserved
              simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved] at observed
              obtain ⟨finalStorage, finalCounts, tailFrame⟩ :=
                ih reachedCaller middle saved middleStorage middleCounts observed
              exact ⟨finalStorage, finalCounts, frame_cons headFrame tailFrame⟩
            | cons second remaining =>
              simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨storage, counts, frame_refl _ _ _⟩

/-- An actual native dispatcher singleton retains the fixed allowed-reference predicate. -/
theorem dispatch_allowed
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (allowed : Nat → Prop) (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries) (after : EnumerationState.State Symbol EnumGuard)
    (valid : ReferencesAllowed allowed before)
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) : ReferencesAllowed allowed after := by
  rcases SourcePruningEnumerationSharedDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨_different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact valid
  · exact SourcePruningEnumerationNativeReferences.assimilated_allowed allowed before source target sourceNode targetNode merged sourceScs targetScs
      valid sourceStored targetStored

/-- Every actual fold endpoint retains the fixed predicate, including rejection and faults. -/
theorem run_allowed
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (allowed : Nat → Prop) (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)))))
    (afterCaller : Caller width) (savedQueries : Queries) (after : EnumerationState.State Symbol Constraint)
    (valid : ReferencesAllowed allowed before)
    (observed : SourcePruningEnumerationSharedCachedTerminal.rawFold checkEmpty nativeFuel p h sources
      beforeCaller before target queries = (result, afterCaller, savedQueries, after)) : ReferencesAllowed allowed after := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
    simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, Prod.mk.injEq] at observed
    rcases observed with ⟨rfl, rfl, rfl, rfl⟩
    exact valid
  | cons source rest ih =>
    rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
    cases dispatchResult with
    | error fault =>
      simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact valid
    | ok possible =>
      cases possible with
      | none =>
        simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, Prod.mk.injEq] at observed
        rcases observed with ⟨rfl, rfl, rfl, rfl⟩
        exact valid
      | some action =>
        cases rawObserved : ExceptT.run (action before) with
        | nil =>
          simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact valid
        | cons head tail =>
          cases head with
          | error error =>
            simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
            rcases observed with ⟨rfl, rfl, rfl, rfl⟩
            exact valid
          | ok pair =>
            rcases pair with ⟨valueUnit, middle⟩
            cases valueUnit
            cases tail with
            | nil =>
              have middleValid := dispatch_allowed allowed checkEmpty nativeFuel p h beforeCaller before
                source target queries action reachedCaller saved middle valid dispatchObserved rawObserved
              simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved] at observed
              exact ih reachedCaller middle saved middleValid observed
            | cons second remaining =>
              simp only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact valid

end MicroCFTA.SourcePruningEnumerationSharedFoldState
