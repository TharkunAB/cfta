import MicroCFTA.SourceEqualityIntersectionEdgeAllocation
import MicroCFTA.SourceEqualityConstraintFieldLookup

/-!
# Plain guards at actual checked conjunctions

Each closure law uses only the two queried guards. Actual field loads retain
their original readback. A ready allocated conjunction retains the same plain
test. These laws require no annotation condition on unrelated heap records.
-/
namespace MicroCFTA.SourceCurrentUnconstrainedGuardClosure
open Language SourceGuards SourceSymbolicIndex SourceCompactGuards
open SourceEqualityConstraintAllocation
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula

private theorem active_leaf_empty (classes : EqualityNormalize.Constraints)
    (active : EqualityNormalize.Active classes)
    (accepted : classes.all (SymbolicDriver.classTest (.node () [])) = true) : classes = [] := by
  have satisfied := (SymbolicEqualityBridge.active_classes_exact (.node () []) classes active).mp accepted
  cases classes with
  | nil => rfl
  | cons first rest =>
      obtain ⟨left, leftMember, right, rightMember, different⟩ := active first List.mem_cons_self
      obtain ⟨value, atLeft, atRight⟩ := satisfied first List.mem_cons_self left leftMember right rightMember different
      have leftEmpty : left = [] := by cases left <;> simp_all [Term.atPath]
      have rightEmpty : right = [] := by cases right <;> simp_all [Term.atPath]
      exact False.elim (different (leftEmpty.trans rightEmpty.symm))

private theorem active_option_leaf_empty (classes : Option EqualityNormalize.Constraints)
    (active : ActiveOption classes)
    (accepted : ConstraintIndicators.equalityValue (SymbolicDriver.classTest (.node () [])) classes = true) :
    classes = some [] := by
  cases classes with
  | none => cases accepted
  | some values => exact congrArg some (active_leaf_empty values (active values rfl) accepted)

mutual
private theorem positive_empty_atoms (guard : SourceGuards.Guard Formula)
    (empty : positive guard = some []) : GuardConjunction.atoms guard = [] := by
  cases guard with
  | top => simp only [GuardConjunction.atoms]
  | and parts => simpa only [GuardConjunction.atoms] using positive_list_empty_atoms parts empty
  | same left right => simp only [positive] at empty; split at empty <;> cases empty
  | bottom | entails | satisfies | holds | substitute | not | or => cases empty

private theorem positive_list_empty_atoms (guards : List (SourceGuards.Guard Formula))
    (empty : positiveList guards = some []) : guards.flatMap GuardConjunction.atoms = [] := by
  cases guards with
  | nil => rfl
  | cons first rest =>
      simp only [positiveList, Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at empty
      obtain ⟨left, head, right, tail, same⟩ := empty
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp same
      simp only [List.flatMap_cons, positive_empty_atoms first head, positive_list_empty_atoms rest tail,
        List.nil_append]
end

/-- Plain normalized guards contain no stored class and no outer guard atom. -/
theorem plain_fields (guard : Guard) (active : ActiveOption guard.equalities)
    (plain : SourceMemoGate.plain guard = true) :
    guard.equalities = some [] ∧ GuardConjunction.atoms guard.guard = [] := by
  have checks := Bool.and_eq_true_iff.mp plain
  have empty : sourceEqualities guard = some [] := of_decide_eq_true checks.1
  have support : (positive guard.guard).isSome = true :=
    (positiveNormalized_support guard.guard).symm.trans checks.2
  obtain ⟨raw, extracted⟩ := Option.isSome_iff_exists.mp support
  obtain ⟨added, found, addedActive, exactAdded⟩ :=
    positiveNormalized_exact (Symbol := Unit) guard.guard raw extracted
  have combined : ConstraintIndicators.equalityValue (SymbolicDriver.classTest (.node () [])) (sourceEqualities guard) =
      (ConstraintIndicators.equalityValue (SymbolicDriver.classTest (.node () [])) guard.equalities &&
        ConstraintIndicators.equalityValue (SymbolicDriver.classTest (.node () [])) added) := by
    cases added with
    | none =>
        cases stored : guard.equalities <;>
          simp only [sourceEqualities, found, stored, combineEqualities, ConstraintIndicators.equalityValue, Bool.and_false]
    | some values =>
        cases values with
        | nil => simp only [sourceEqualities, found, ConstraintIndicators.equalityValue, List.all_nil, Bool.and_true]
        | cons first rest =>
            simpa only [sourceEqualities, found] using combine_value guard.equalities (some (first :: rest)) active addedActive (.node () [])
  rw [empty] at combined
  have values := Bool.and_eq_true_iff.mp combined.symm
  have storedEmpty := active_option_leaf_empty guard.equalities active values.1
  have rawAccepted : raw.all (SymbolicDriver.classTest (.node () [])) = true :=
    (exactAdded (.node () [])).symm.trans values.2
  have rawEmpty := active_leaf_empty raw (positive_active guard.guard raw extracted) rawAccepted
  exact ⟨storedEmpty, positive_empty_atoms guard.guard (rawEmpty ▸ extracted)⟩

/-- The literal sentinel constraint passes the source plain test. -/
theorem top_plain : SourceMemoGate.plain (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)) = true := rfl

/-- Conjunction of the two actual plain guards retains the source plain test. -/
theorem conjoin_plain [DecidableEq (SourceGuards.Guard FullSyntax.Formula)]
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (first second : Guard) (firstActive : ActiveOption first.equalities) (secondActive : ActiveOption second.equalities)
    (firstPlain : SourceMemoGate.plain first = true) (secondPlain : SourceMemoGate.plain second = true) :
    SourceMemoGate.plain (SourceEqualityConstraintConstructors.conjoin le first second) = true := by
  obtain ⟨firstEmpty, firstAtoms⟩ := plain_fields first firstActive firstPlain
  obtain ⟨secondEmpty, secondAtoms⟩ := plain_fields second secondActive secondPlain
  simpa only [SourceEqualityConstraintConstructors.conjoin, firstEmpty, secondEmpty, combineEqualities,
    GuardConjunction.merge, GuardConjunction.normalize, GuardConjunction.atoms, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, firstAtoms, secondAtoms, List.nil_append,
    GuardConjunction.canonical, List.eraseDups_nil, List.mergeSort_nil, GuardConjunction.conjoin,
    SourceEqualityConstraintConstructors.top] using top_plain

/-- A current allocated ready field has nontrivial classes in its literal readback. -/
theorem ready_active (value : Allocated) (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (ready : Ready cache value.stored) : ActiveOption (SourceEqualityConjoinAllocation.readback value).equalities := by
  intro classes same
  cases stored : value.stored with
  | contradiction => simp [SourceEqualityConjoinAllocation.readback, SourceEqualityAccessorAllocation.constraint, stored,
      SourceEqualityInheritedPayload.classes, Value.payload] at same
  | live identity records =>
      have equal : records.map SourceEqualityClassOrder.Record.paths = classes := by
        simpa [SourceEqualityConjoinAllocation.readback, SourceEqualityAccessorAllocation.constraint, stored,
          SourceEqualityInheritedPayload.classes, Value.payload] using same
      subst classes
      intro paths member
      obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
      exact (ready.2 records (by rw [stored]; rfl) record present).2.2

/-- The actual allocated conjunction retains plain readback at its returned candidate. -/
theorem conjoin_result_plain [DecidableEq (SourceGuards.Guard FullSyntax.Formula)]
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (first second : Allocated) (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored)
    (firstPlain : SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback first) = true)
    (secondPlain : SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback second) = true)
    (result : Allocated) (done : (SourceEqualityConjoinAllocation.conjoin le first second before).1 = .ok result) :
    SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback result) = true := by
  obtain ⟨actual, completed, _, _, same, _, _, _⟩ :=
    SourceEqualityConjoinAllocation.conjoin_correct le first second before valid firstReady secondReady
  have equal : actual = result := Except.ok.inj (completed.symm.trans done)
  subst actual
  rw [same]
  exact conjoin_plain le _ _ (ready_active first _ firstReady) (ready_active second _ secondReady) firstPlain secondPlain

/-- A ready checked intersection returns the plain conjunction of its two loaded guards. -/
theorem ready_plain [DecidableEq (SourceGuards.Guard FullSyntax.Formula)]
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (first second : Allocated) (firstArity secondArity : Nat) (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored)
    (firstPlain : SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback first) = true)
    (secondPlain : SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback second) = true)
    (result : Allocated)
    (done : (SourceEqualityIntersectionEdgeAllocation.run le first second firstArity secondArity before).1 = .ok (.ready result)) :
    SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback result) = true := by
  obtain ⟨branch, completed, mapped, _, _, _⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct le first second firstArity secondArity before valid firstReady secondReady
  have equal : branch = .ready result := Except.ok.inj (completed.symm.trans done)
  subst branch
  simp only [SourceEqualityIntersectionEdgeAllocation.Branch.map, SourceEqualityIntersectionEdgeAllocation.source] at mapped
  split at mapped
  · cases mapped
  · split at mapped
    · have same := SourceEqualityIntersectionEdgeAllocation.Branch.ready.inj mapped
      rw [same]
      exact conjoin_plain le _ _ (ready_active first _ firstReady) (ready_active second _ secondReady) firstPlain secondPlain
    · cases mapped

/-- Current original field loads supply plain closure for their exact checked ready result. -/
theorem loaded_ready_plain [DecidableEq (SourceGuards.Guard FullSyntax.Formula)]
    (le : SourceGuards.Guard FullSyntax.Formula → SourceGuards.Guard FullSyntax.Formula → Bool)
    (left right : Guard) (first second : Allocated) (firstArity secondArity : Nat)
    (before : SourceEqualityConstraintMemoAllocation.State) (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (leftCached : SourceEqualityGuardReadback.Cached left.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached right.equalities)
    (leftLoad : SourceEqualityConstraintFieldLookup.load left before.constraints = .ok (some first))
    (rightLoad : SourceEqualityConstraintFieldLookup.load right before.constraints = .ok (some second))
    (leftPlain : SourceMemoGate.plain left = true) (rightPlain : SourceMemoGate.plain right = true)
    (result : Allocated)
    (done : (SourceEqualityIntersectionEdgeAllocation.run le first second firstArity secondArity before).1 = .ok (.ready result)) :
    SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback result) = true := by
  obtain ⟨firstReady, firstReadback⟩ := SourceEqualityConstraintFieldLookup.load_ready left before.constraints valid.constraints leftCached first leftLoad
  obtain ⟨secondReady, secondReadback⟩ := SourceEqualityConstraintFieldLookup.load_ready right before.constraints valid.constraints rightCached second rightLoad
  exact ready_plain le first second firstArity secondArity before valid firstReady secondReady
    (firstReadback ▸ leftPlain) (secondReadback ▸ rightPlain) result done

end MicroCFTA.SourceCurrentUnconstrainedGuardClosure
