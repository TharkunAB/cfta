import MicroCFTA.SourceCurrentConjunctionDemandWorklistSoundness
import MicroCFTA.SourceCurrentConjunctionDemandWorklistNumeric
import MicroCFTA.SourceCurrentConjunctionDemandWorklistEffects

/-!
# Sound fourth-memo calls for actual demand decisions

A hit reads the existing memo before any demand sampling. A miss runs the
actual demand decision and inserts only its completed answer. The proof
retains the returned physical state, existing entries, and the same semantic
memo predicate. Initial completion needs readiness and query availability.
It does not require a future result or a numeric heap certificate.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandMemo
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentEmptinessMemo (Memo AnswerSound Correct Extends)
open SourceCurrentConjunctionDemandWorklistExecution (Call)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- An initial ready query derives a completed graph of its actual demand call. -/
theorem complete (budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap query) :
    ∃ answer after saved, Call budget memo query before answer after saved ∧ Effects before after :=
  SourceCurrentConjunctionDemandWorklistNumeric.call_initial budget memo query before ready available

/-- Actual demand-call graphs derive sound answers and retain all previous valid entries. -/
theorem verified (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {query : Node} {before after : Physical} {answer : Bool} {memo saved : Memo}
    (call : Call budget memo query before answer after saved) (ready : Ready before)
    (available : Available before.heap query) (correct : Correct formulas solver before.heap memo) :
    Effects before after ∧ Correct formulas solver after.heap saved ∧
      AnswerSound formulas solver query answer ∧ Extends memo saved := by
  cases call with
  | hit found =>
      obtain ⟨identity, originalAvailable, sound⟩ := correct _ _ _ found
      have same := InternedFreshProbeKeys.resident_reference_injective before.heap
        ready.semantic.ready.semantic.1.normal.facts.coherent _ query
        originalAvailable.resident available.resident identity
      subst_vars
      exact ⟨Effects.refl before ready, correct, sound, fun _ _ present => present⟩
  | miss absent actual =>
      have checked := SourceCurrentConjunctionDemandWorklistExecution.Decision.verified actual ready available formulas solver
      have effects := checked.1
      have sound := checked.2
      have old := SourceCurrentEmptinessMemo.grows formulas solver effects.keeps memo correct
      refine ⟨effects, ?_, sound, ?_⟩
      · intro key original result found
        dsimp only [SourceCurrentEmptinessMemo.insert] at found
        split at found
        · rename_i same
          have pair : query = original ∧ answer = result := by
            simpa only [Option.some.injEq, Prod.mk.injEq] using found
          rcases pair with ⟨rfl, rfl⟩
          exact ⟨same.symm, effects.keeps.available query available, sound⟩
        · exact old key original result found
      · intro key entry found
        have different : key ≠ query.referenceOf := by
          intro same
          subst key
          rw [absent] at found
          cases found
        simp only [SourceCurrentEmptinessMemo.insert, different, ↓reduceIte, found]

/-- Initial valid memo state supplies a completed call with its returned invariants. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap query) (correct : Correct formulas solver before.heap memo) :
    ∃ answer after saved, Call budget memo query before answer after saved ∧ Effects before after ∧
      Correct formulas solver after.heap saved ∧ AnswerSound formulas solver query answer ∧ Extends memo saved := by
  obtain ⟨answer, after, saved, actual, _⟩ := complete budget memo query before ready available
  exact ⟨answer, after, saved, actual, verified formulas solver actual ready available correct⟩

/-- Every observed successful physical demand call satisfies the same memo contract. -/
theorem actual_verified (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {p h budget : Nat} {query : Node} {before after : Physical} {answer : Bool} {memo saved : Memo}
    (actual : SourceCurrentConjunctionDemandWorker.call p h budget memo query before = .done (answer, saved) after)
    (ready : Ready before) (available : Available before.heap query) (correct : Correct formulas solver before.heap memo) :
    Effects before after ∧ Correct formulas solver after.heap saved ∧
      AnswerSound formulas solver query answer ∧ Extends memo saved :=
  verified formulas solver (SourceCurrentConjunctionDemandWorklistExecution.call_graph actual) ready available correct

/-- Successful returns validate the saved memo. Failure retains the original memo. -/
def OutcomeCorrect (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (memo : Memo) (query : Node) :
    SourceCurrentConjunctionWorker.Outcome Symbol FullSyntax.Formula (Bool × Memo) → Prop
  | .done (answer, saved) after =>
      Correct formulas solver after.heap saved ∧ AnswerSound formulas solver query answer ∧ Extends memo saved
  | .failed _ after => Correct formulas solver after.heap memo

/-- Every literal call outcome retains its applicable memo and physical invariants. -/
theorem call_outcome (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (p h budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap query) (correct : Correct formulas solver before.heap memo) :
    Effects before (SourceCurrentConjunctionDemandWorker.call p h budget memo query before).state ∧
      OutcomeCorrect formulas solver memo query (SourceCurrentConjunctionDemandWorker.call p h budget memo query before) := by
  have effects : Effects before (SourceCurrentConjunctionDemandWorker.call p h budget memo query before).state :=
    Eq.mp (by congr <;> exact Subsingleton.elim _ _)
      (SourceCurrentConjunctionDemandWorklistEffects.call_effects p h budget memo query before ready available)
  cases actual : SourceCurrentConjunctionDemandWorker.call p h budget memo query before with
  | done output after =>
      rcases output with ⟨answer, saved⟩
      exact actual_verified formulas solver actual ready available correct
  | failed fault after =>
      have kept : Effects before after := by
        simpa only [actual, SourceCurrentConjunctionWorker.Outcome.state] using effects
      exact ⟨kept, SourceCurrentEmptinessMemo.grows formulas solver kept.keeps memo correct⟩

end MicroCFTA.SourceCurrentConjunctionDemandMemo
