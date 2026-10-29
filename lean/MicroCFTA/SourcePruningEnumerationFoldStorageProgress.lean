import MicroCFTA.SourcePruningEnumerationMixedStorageProgress
import MicroCFTA.SourcePruningEnumerationDispatchShape
import MicroCFTA.SourcePruningEnumerationFold

namespace MicroCFTA.SourcePruningEnumerationDispatch
open Language EnumerationState EnumerationCorrectness EnumerationCompleteness EnumerationStorageProgress
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual same-term merge cannot increase pending size or remove its pending target. -/
theorem singleton_pendingSize_le
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : Core EnumGuard) (source target : Nat)
    (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries) (after : Core EnumGuard)
    (assignment : Nat → Term Symbol)
    (equal : assignment source = assignment target)
    (selected : dispatch checkEmpty nativeFuel p h beforeCaller before source target queries =
      (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    pendingSize after assignment ≤ pendingSize before assignment ∧
      after.representatives = before.representatives ∧
      (PendingAt before target → PendingAt after target) := by
  rcases SourcePruningEnumerationDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact ⟨Nat.le_refl _, rfl, id⟩
  · have targetInside := (List.getElem?_eq_some_iff.mp targetStored).1
    have sourceInside := (List.getElem?_eq_some_iff.mp sourceStored).1
    have pending := (assimilated_pending before target source merged (sourceScs ++ targetScs)
      (Ne.symm different) targetInside sourceInside).1
    refine ⟨?_, rfl, fun _ => pending⟩
    by_cases supported : sourceNode.isSome = true ∨ targetNode.isSome = true
    · exact assimilated_pendingSize_le before source target sourceNode targetNode merged
        sourceScs targetScs assignment (Ne.symm different) sourceStored targetStored equal (fun _ => supported)
    · have sourceNone : sourceNode = none := by cases sourceNode <;> simp_all
      have targetNone : targetNode = none := by cases targetNode <;> simp_all
      subst sourceNode
      subst targetNode
      simp only [dispatch, ite_eq_right different, sourceStored, targetStored, Id.run, pure,
        Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
      rcases selected with ⟨rfl, rfl, rfl⟩
      have actual : assimilated before target source (.unenumerated none (sourceScs ++ targetScs)) =
          assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)) := by
        simpa only [finishOptional, reduceCtorEq, ↓reduceIte, ExceptT.run,
          List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] using completed
      rw [← actual]
      exact assimilated_pendingSize_le before source target none none none sourceScs targetScs
        assignment (Ne.symm different) sourceStored targetStored equal (by intro impossible; cases impossible)

end MicroCFTA.SourcePruningEnumerationDispatch

namespace MicroCFTA.SourcePruningEnumerationFold
open Language EnumerationState EnumerationCorrectness EnumerationCompleteness EnumerationStorageProgress
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual successful fold retains a pending target and cannot increase its fixed assignment's cost. -/
theorem singleton_pendingSize_le
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Core EnumGuard) (target : Nat) (queries : Queries)
    (afterCaller : Caller width) (savedQueries : Queries) (after : Core EnumGuard)
    (assignment : Nat → Term Symbol) (targetPending : PendingAt before target)
    (equal : ∀ source ∈ sources, assignment source = assignment target)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (.ok (some [.ok ((), after)]), afterCaller, savedQueries, after)) :
    PendingAt after target ∧ after.representatives = before.representatives ∧
      pendingSize after assignment ≤ pendingSize before assignment := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      have same := congrArg (fun result => result.2.2.2) observed
      change before = after at same
      rw [← same]
      exact ⟨targetPending, rfl, Nat.le_refl _⟩
  | cons source rest ih =>
      rcases selected : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨result, reachedCaller, saved⟩
      cases result with
      | error fault => simp only [run, selected] at observed; cases observed
      | ok possible =>
          cases possible with
          | none => simp only [run, selected] at observed; cases observed
          | some action =>
              cases raw : ExceptT.run (action before) with
              | nil => simp only [run, selected, raw] at observed; cases observed
              | cons first tail =>
                  cases first with
                  | error fault => simp only [run, selected, raw] at observed; cases observed
                  | ok pair =>
                      rcases pair with ⟨ignored, middle⟩
                      cases ignored
                      cases tail with
                      | cons second remaining =>
                          simp only [run, selected, raw] at observed
                          cases observed
                      | nil =>
                          simp only [run, selected, raw] at observed
                          have step := SourcePruningEnumerationDispatch.singleton_pendingSize_le
                            checkEmpty nativeFuel p h beforeCaller before source target queries action
                            reachedCaller saved middle assignment (equal source List.mem_cons_self) selected raw
                          have tailEqual : ∀ next ∈ rest, assignment next = assignment target :=
                            fun next member => equal next (List.mem_cons_of_mem source member)
                          have continued := ih reachedCaller middle saved (step.2.2 targetPending) tailEqual observed
                          exact ⟨continued.1, continued.2.1.trans step.2.1, Nat.le_trans continued.2.2 step.1⟩

end MicroCFTA.SourcePruningEnumerationFold
