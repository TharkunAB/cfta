import MicroCFTA.SourceCurrentConjunctionSharedWorklistWeight

/-!
# Actual progress after a conjunction is forced

Ordinary visits remove one finite queue task. Positive raw sampling and
overflow strictly reduce the remaining tuple budget. The vector keeps the
original budget as its fixed dimension. No additional allowance is supplied.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistVisitProgress
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorklistStep
open SourceCurrentConjunctionSharedWorklistWeight
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "closed" => SourceCurrentConjunctionWorklist.closed
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- A completed visit lowers the source budget or its finite queue vector. -/
theorem visit_decreases (bound h : Nat) (credits added : List Nat)
    (nodes : List Node) (rest : List (Task Symbol Formula)) (before after : State Symbol Formula)
    (present : RowsPresent credits rest)
    (removed : HeightOrder.VectorBelow (bound + 2)
      (rank bound credits rest) (rank bound credits before.pending))
    (actual : visit h nodes rest before = .done .more after) :
    Prod.Lex (fun first last : Nat => first < last) (HeightOrder.VectorBelow (bound + 2))
      (after.budget, rank bound (credits ++ added) after.pending)
      (before.budget, rank bound credits before.pending) := by
  have sameRank : rank bound (credits ++ added) rest = rank bound credits rest := by
    funext index
    exact congrFun (weight_append_credits credits added rest present) index.val
  cases empty : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
  | true =>
      rw [visit_empty h nodes rest before empty] at actual
      cases actual
      apply Prod.Lex.right
      change HeightOrder.VectorBelow (bound + 2) (rank bound (credits ++ added) rest)
        (rank bound credits before.pending)
      rw [sameRank]
      exact removed
  | false =>
      cases fresh : SourceCurrentConjunctionEmptinessTable.skip key closed before.budget
          (queryTable before.table) nodes with
      | true =>
          rw [visit_skip h nodes rest before empty fresh] at actual
          cases actual
          apply Prod.Lex.right
          change HeightOrder.VectorBelow (bound + 2) (rank bound (credits ++ added) rest)
            (rank bound credits before.pending)
          rw [sameRank]
          exact removed
      | false =>
          cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h before.budget nodes
              before.storage.requirements.physical with
          | failed fault physical =>
              rw [visit_failed h nodes rest before physical fault empty fresh sampled] at actual
              cases actual
          | done result physical =>
              cases result with
              | overflow tuples cursor =>
                  have positive := (SourceCurrentConjunctionEmptinessTable.admitted key closed before.budget
                    (queryTable before.table) nodes fresh).1
                  rw [visit_overflow h nodes rest before physical tuples cursor empty fresh sampled] at actual
                  cases actual
                  apply Prod.Lex.left
                  exact positive
              | fit tuples =>
                  cases tuples with
                  | nil =>
                      rw [visit_zero h nodes rest before physical empty fresh sampled] at actual
                      cases actual
                      apply Prod.Lex.right
                      change HeightOrder.VectorBelow (bound + 2) (rank bound (credits ++ added) rest)
                        (rank bound credits before.pending)
                      rw [sameRank]
                      exact removed
                  | cons tuple tuples =>
                      have bounded := SourceCurrentConjunctionTuplePullTotal.sample_bounded h before.budget nodes
                        before.storage.requirements.physical physical (.fit (tuple :: tuples)) sampled
                      simp only [SourceCurrentConjunctionTuplePullTotal.Result.toStatus,
                        SourceCurrentConjunctionTuplePullAdmission.Bounded, List.length_cons] at bounded
                      rw [visit_positive h nodes rest before physical tuple tuples empty fresh sampled] at actual
                      cases actual
                      apply Prod.Lex.left
                      change before.budget - (tuples.length + 1) < before.budget
                      omega

end MicroCFTA.SourceCurrentConjunctionSharedWorklistVisitProgress
