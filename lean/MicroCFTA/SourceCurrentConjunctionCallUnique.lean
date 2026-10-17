import MicroCFTA.SourceCurrentConjunctionWorkerCompletion

/-!
# Exact return uniqueness for the actual conjunction memo call

Both actual graphs execute the same worker at common larger bounds.
Worker determinism fixes the Boolean, full physical state, and saved memo.
This is a graph verification lemma. It does not construct an initial call.
-/
namespace MicroCFTA.SourceCurrentConjunctionCallUnique
open InternedConstructorTemplates
open SourceCurrentConjunctionWorker (Outcome)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Two actual calls from identical inputs return the same answer, physical state, and saved memo. -/
theorem call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {memo firstSaved secondSaved : Memo} {query : Value Symbol Guard}
    {before firstAfter secondAfter : Physical} {firstAnswer secondAnswer : Bool}
    (first : SourceCurrentConjunctionMemo.Call budget memo query before firstAnswer firstAfter firstSaved)
    (second : SourceCurrentConjunctionMemo.Call budget memo query before secondAnswer secondAfter secondSaved) :
    firstAnswer = secondAnswer ∧ firstAfter = secondAfter ∧ firstSaved = secondSaved := by
  obtain ⟨firstP, firstH, firstStable⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete first
  obtain ⟨secondP, secondH, secondStable⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete second
  have firstAt := firstStable (max firstP secondP) (max firstH secondH)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have secondAt := secondStable (max firstP secondP) (max firstH secondH)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  obtain ⟨pair, state⟩ := Outcome.done.inj (firstAt.symm.trans secondAt)
  obtain ⟨answer, saved⟩ := Prod.mk.inj pair
  exact ⟨answer, state, saved⟩

end MicroCFTA.SourceCurrentConjunctionCallUnique
