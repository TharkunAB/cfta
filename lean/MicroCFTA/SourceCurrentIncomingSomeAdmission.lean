import MicroCFTA.SourceCurrentIncomingReadStorage

/-! Literal optional cache success derives original slot and row-shape admissions. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingSomeAdmission
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
variable {width : Nat}

/-- Original storage derives allocation and old-reference bounds from the observed original slot. -/
theorem stored_admissions (before : Core) (target : Nat) (oldNode : Option Nat)
    (scs oldScs : List Suspended) (storage : StorageValid before)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (incomingBound : ∀ sc ∈ scs, sc.var < before.counter) :
    target < before.counter ∧ ∀ sc ∈ scs ++ oldScs, sc.var < before.counter := by
  obtain ⟨insideValues, _valueSame⟩ := List.getElem?_eq_some_iff.mp stored
  have oldBound := storage.values (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored)
  change (∀ sc ∈ oldScs, sc.var < before.counter) at oldBound
  refine ⟨?_, ?_⟩
  · rw [storage.aligned]
    exact insideValues
  · intro sc member
    rcases List.mem_append.mp member with added | retained
    · exact incomingBound sc added
    · exact oldBound sc retained

/-- An actual optional cache result derives the original stored unenumerated slot. -/
theorem some_stored (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h k target : Nat) (caller : Caller width) (before after : Cached)
    (incoming : Node) (scs : List Suspended) (queries : SourceEndpointMemo.Memos)
    (rooted : IsRoot before.core.representatives target) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs queries).2 = some after →
    ∃ oldNode oldScs, before.core.values[target]? = some (.unenumerated oldNode oldScs) := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  intro observed
  cases rootRead : UnionFind.findRoot r before.core.representatives target with
  | none =>
      simp [SourcePruningEnumerationIncomingCacheAdapter.run, SourcePruningEnumerationIncomingNode.run,
        rootRead, SourcePruningEnumerationIncomingCacheAdapter.adapt] at observed
  | some found =>
      have rootSame := SourceCurrentIncomingOriginalRoot.original_target before.core.representatives
        r target rooted found rootRead
      cases stored : before.core.values[target]? with
      | none =>
          simp [SourcePruningEnumerationIncomingCacheAdapter.run, SourcePruningEnumerationIncomingNode.run,
            rootRead, rootSame, stored, SourcePruningEnumerationIncomingCacheAdapter.adapt] at observed
      | some value =>
          cases value with
          | unenumerated oldNode oldScs => exact ⟨oldNode, oldScs, rfl⟩
          | eliminated =>
              simp [SourcePruningEnumerationIncomingCacheAdapter.run, SourcePruningEnumerationIncomingNode.run,
                rootRead, rootSame, stored, SourcePruningEnumerationIncomingCacheAdapter.adapt] at observed
          | enumerated fragment =>
              simp [SourcePruningEnumerationIncomingCacheAdapter.run, SourcePruningEnumerationIncomingNode.run,
                rootRead, rootSame, stored, SourcePruningEnumerationIncomingCacheAdapter.adapt] at observed

/-- Actual optional cache success permits exactly the literal empty or successful singleton row shape. -/
theorem some_rows (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h k target : Nat) (caller : Caller width) (before after : Cached)
    (incoming : Node) (scs : List Suspended) (queries : SourceEndpointMemo.Memos) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs queries
    actual.2 = some after →
      actual.1.1 = .ok (some []) ∨ ∃ returned, actual.1.1 = .ok (some [.ok ((), returned)]) := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  intro observed
  simp only [SourcePruningEnumerationIncomingCacheAdapter.run] at observed ⊢
  generalize actualRun : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before.core target incoming scs queries = actual at observed ⊢
  rcases actual with ⟨result, reached, savedQueries, read⟩
  cases result with
  | error fault => simp at observed
  | ok output =>
      cases output with
      | none => simp at observed
      | some rows =>
          dsimp only at observed ⊢
          cases rows with
          | nil => exact Or.inl rfl
          | cons first rest =>
              cases rest with
              | cons second tail => simp [SourcePruningEnumerationIncomingCacheAdapter.adapt] at observed
              | nil =>
                  cases first with
                  | error fault => simp [SourcePruningEnumerationIncomingCacheAdapter.adapt] at observed
                  | ok payload =>
                      rcases payload with ⟨resultUnit, returned⟩
                      cases resultUnit
                      exact Or.inr ⟨returned, rfl⟩

end MicroCFTA.SourceCurrentIncomingSomeAdmission
