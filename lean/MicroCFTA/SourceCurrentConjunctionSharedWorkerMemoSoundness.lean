import MicroCFTA.SourceCurrentConjunctionSharedWorkerSoundness
import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects

/-!
# Conservative answers in the actual shared memo call

Current memo correctness certifies hits. Current readiness identifies the
stored query by its resident reference. Actual successful misses derive the
decision law and publish that exact query and answer. Earlier completed
entries retain their values. Failed calls publish no completed result.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerMemoSoundness
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorker (call decision Outcome)
open SourceCurrentEmptinessMemo (Memo Correct AnswerSound Extends)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Each actual successful call preserves completed entries and its conservative answer law. -/
theorem call_sound (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {p h budget : Nat} {memo saved : Memo} {query : Node} {before : Physical}
    {after : WorkState} {answer : Bool}
    (actual : call p h budget memo query before = .done (answer, saved) after)
    (ready : Ready before) (available : Available before.heap query)
    (correct : Correct formulas solver before.heap memo) :
    Correct formulas solver after.storage.requirements.physical.heap saved ∧
      AnswerSound formulas solver query answer ∧ Extends memo saved := by
  cases hit : memo query.referenceOf with
  | some entry =>
      rcases entry with ⟨original, result⟩
      obtain ⟨identity, originalAvailable, sound⟩ := correct _ _ _ hit
      have same : original = query := InternedFreshProbeKeys.resident_reference_injective before.heap
        ready.semantic.ready.semantic.1.normal.facts.coherent original query
        originalAvailable.resident available.resident identity
      subst original
      rw [SourceCurrentConjunctionSharedWorker.call_hit p h budget memo query query before result hit] at actual
      cases actual
      exact ⟨correct, sound, fun _ _ found => found⟩
  | none =>
      cases decided : decision p h budget query before with
      | failed fault reached =>
          rw [SourceCurrentConjunctionSharedWorker.call_failed p h budget memo query before reached fault hit decided] at actual
          cases actual
      | done result reached =>
          have effects : Effects before reached.storage.requirements.physical := by
            simpa only [decided, Outcome.state] using
              (SourceCurrentConjunctionSharedWorkerEffects.decision_effects p h budget query before ready available).1
          have sound := SourceCurrentConjunctionSharedWorkerSoundness.decision_answer_sound
            formulas solver decided ready available
          have old := SourceCurrentEmptinessMemo.grows formulas solver effects.keeps memo correct
          rw [SourceCurrentConjunctionSharedWorker.call_done p h budget memo query before reached result hit decided] at actual
          cases actual
          refine ⟨?_, sound, ?_⟩
          · intro key original answer found
            dsimp only [SourceCurrentEmptinessMemo.insert] at found
            split at found
            · rename_i same
              rcases Prod.mk.inj (Option.some.inj found) with ⟨rfl, rfl⟩
              exact ⟨same.symm, effects.keeps.available query available, sound⟩
            · exact old key original answer found
          · intro key entry found
            have different : key ≠ query.referenceOf := by
              intro same
              subst key
              rw [hit] at found
              cases found
            simp only [SourceCurrentEmptinessMemo.insert, different, ite_false, found]

/-- Current original inputs and memo correctness derive every successful call's memo contract. -/
theorem call_verified (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (p h budget : Nat)
    (memo : Memo) (query : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap query)
    (correct : Correct formulas solver before.heap memo) :
    match call p h budget memo query before with
    | .failed _ _ => True
    | .done result after =>
        Correct formulas solver after.storage.requirements.physical.heap result.2 ∧
          AnswerSound formulas solver query result.1 ∧ Extends memo result.2 := by
  cases actual : call p h budget memo query before with
  | failed fault after => trivial
  | done result after =>
      rcases result with ⟨answer, saved⟩
      exact call_sound formulas solver actual ready available correct

end MicroCFTA.SourceCurrentConjunctionSharedWorkerMemoSoundness
