import MicroCFTA.SourceEqualityConjoinAllocation
import MicroCFTA.SourceEqualityMkEdgeAllocation

/-!
# Equality allocation before intersection child demand

The source rejects unequal arities before conjunction. Equal arities conjoin
raw stored constraints and run the checked edge guard. Rejection retains
every reached allocation. Children are absent from this prefix model.
Ready output records the constraint for a later child-demand continuation.
-/
namespace MicroCFTA.SourceEqualityIntersectionEdgeAllocation
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (State Valid Grows)
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint
local notation "SourceConstraint" => SourceSymbolicIndex.Constraint

/-- The constructor prefix distinguishes arity mismatch, guard rejection, and a ready constraint. -/
inductive Branch (Constraint : Type) where
  | mismatch
  | rejected
  | ready (constraint : Constraint)

/-- Read the constraint of a ready branch without changing either stopping branch. -/
def Branch.map (read : First → Second) : Branch First → Branch Second
  | .mismatch => .mismatch
  | .rejected => .rejected
  | .ready constraint => .ready (read constraint)

/-- The existing complete source checks determine the exact prefix outcome. -/
noncomputable def source [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : SourceConstraint Formula) (firstArity secondArity : Nat) : Branch (SourceConstraint Formula) :=
  if firstArity ≠ secondArity then .mismatch
  else
    let combined := SourceEqualityConstraintConstructors.conjoin le first second
    if SourceEqualityMkEdgeAllocation.accepted combined firstArity then .ready combined else .rejected

/-- Execute the source prefix without representing or evaluating any child intersection. -/
noncomputable def run [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Allocated Formula) (firstArity secondArity : Nat) (before : State) :
    Except String (Branch (Allocated Formula)) × State :=
  if firstArity ≠ secondArity then (.ok .mismatch, before)
  else
    let combined := SourceEqualityConjoinAllocation.conjoin le first second before
    match combined.1 with
    | .error message => (.error message, combined.2)
    | .ok constraint =>
        let checked := SourceEqualityMkEdgeAllocation.check constraint.stored constraint.guard firstArity combined.2
        match checked.1 with
        | .error message => (.error message, checked.2)
        | .ok keep => (.ok (if keep then .ready constraint else .rejected), checked.2)

/-- An arity mismatch skips conjunction and the full accessor with identical operation state. -/
theorem run_mismatch [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Allocated Formula) (firstArity secondArity : Nat) (before : State)
    (mismatch : firstArity ≠ secondArity) :
    run le first second firstArity secondArity before = (.ok .mismatch, before) := by
  unfold run
  exact ite_eq_left mismatch

private theorem grows_trans {before middle after : State} (first : Grows before middle) (second : Grows middle after) :
    Grows before after :=
  ⟨steps_trans first.constraints second.constraints, Cache.extends_trans first.combinations second.combinations,
    Cache.extends_trans first.descents second.descents⟩

/-- The completed prefix has exact source checks and retains all allocations before its outcome. -/
theorem run_correct [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : Allocated Formula) (firstArity secondArity : Nat) (before : State) (valid : Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored) :
    ∃ branch, (run le first second firstArity secondArity before).1 = .ok branch ∧
      branch.map SourceEqualityConjoinAllocation.readback =
        source le (SourceEqualityConjoinAllocation.readback first) (SourceEqualityConjoinAllocation.readback second) firstArity secondArity ∧
      Valid (run le first second firstArity secondArity before).2 ∧
      Grows before (run le first second firstArity secondArity before).2 ∧
      ∀ result, branch = .ready result →
        Ready (run le first second firstArity secondArity before).2.constraints result.stored ∧
        SourceEqualityGuardReadback.Cached (SourceEqualityConjoinAllocation.readback result).equalities ∧
        SourceEqualityPhysicalPayload.read (SourceEqualityConjoinAllocation.readback result).equalities = .ok result.stored.payload := by
  by_cases mismatch : firstArity ≠ secondArity
  · rw [run_mismatch le first second firstArity secondArity before mismatch]
    refine ⟨.mismatch, rfl, ?_, valid, SourceEqualityConstraintMemoAllocation.grows_refl before, ?_⟩
    · unfold Branch.map source
      exact (ite_eq_left mismatch).symm
    · intro result impossible
      cases impossible
  · obtain ⟨combined, combinedDone, combinedValid, combinedReady, combinedReadback, cached, built, combinedGrows⟩ :=
      SourceEqualityConjoinAllocation.conjoin_correct le first second before valid firstReady secondReady
    obtain ⟨checkedDone, checkedValid, checkedGrows⟩ := SourceEqualityMkEdgeAllocation.check_correct
      combined.stored combined.guard firstArity (SourceEqualityConjoinAllocation.conjoin le first second before).2
      combinedValid combinedReady
    change (SourceEqualityMkEdgeAllocation.check combined.stored combined.guard firstArity
      (SourceEqualityConjoinAllocation.conjoin le first second before).2).1 =
        .ok (SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback combined) firstArity) at checkedDone
    have ready := combinedReady.grows checkedGrows.constraint_growth
    have literal : SourceEqualityPhysicalPayload.read (SourceEqualityConjoinAllocation.readback combined).equalities =
        .ok combined.stored.payload := by rw [combinedReadback]; exact built
    cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback combined) firstArity with
    | false =>
        simp only [run, mismatch, ↓reduceIte, combinedDone, checkedDone, keep, Bool.false_eq_true]
        refine ⟨.rejected, rfl, ?_, checkedValid, grows_trans combinedGrows checkedGrows, ?_⟩
        · simp only [Branch.map, source, mismatch, ↓reduceIte, ← combinedReadback, keep, Bool.false_eq_true]
        · intro result impossible
          cases impossible
    | true =>
        simp only [run, mismatch, ↓reduceIte, combinedDone, checkedDone, keep]
        refine ⟨.ready combined, rfl, ?_, checkedValid, grows_trans combinedGrows checkedGrows, ?_⟩
        · simp only [Branch.map, source, mismatch, ↓reduceIte, ← combinedReadback, keep]
        · intro result same
          cases same
          exact ⟨ready, cached, literal⟩

end MicroCFTA.SourceEqualityIntersectionEdgeAllocation
