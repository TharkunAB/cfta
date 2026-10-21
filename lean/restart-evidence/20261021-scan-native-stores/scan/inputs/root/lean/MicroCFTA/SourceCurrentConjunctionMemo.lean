import MicroCFTA.SourceCurrentConjunctionDecisionSoundness

/-!
# Completed memo calls for conjunction emptiness

Misses run the allocated conjunction Decision. Hits retain both physical
states. The earlier memo record and semantic predicate are reused, but
the historical intersection-based Call is not used.
Pending thunks, publication, native-state transfer, and GHC forcing remain
separate runtime obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionMemo
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentEmptinessMemo (Memo AnswerSound Correct Extends)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula

/-- Lookup precedes the body guard, and misses execute the new allocated decision. -/
inductive Call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Value]
    (budget : Nat) : Memo → Value → Physical → Bool → Physical → Memo → Prop where
  | hit (found : memo query.referenceOf = some (original, answer)) : Call budget memo query before answer before memo
  | miss (absent : memo query.referenceOf = none)
      (actual : SourceCurrentConjunctionDecision.Decision budget query before answer after) :
      Call budget memo query before answer after (SourceCurrentEmptinessMemo.insert memo query answer)

/-- A ready physical query constructs its actual completed hit or miss. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Value]
    (budget : Nat) (memo : Memo) (query : Value) (before : Physical)
    (ready : Ready before) (available : Available before.heap query) :
    ∃ answer after saved, Call budget memo query before answer after saved ∧ Effects before after := by
  cases found : memo query.referenceOf with
  | none =>
      obtain ⟨answer, after, actual, effects⟩ := SourceCurrentConjunctionDecision.complete budget query before ready available
      exact ⟨answer, after, SourceCurrentEmptinessMemo.insert memo query answer, .miss found actual, effects⟩
  | some entry =>
      obtain ⟨original, answer⟩ := entry
      exact ⟨answer, before, memo, .hit found, Effects.refl before ready⟩

/-- An actual new-body call derives sound answers, retained entries, and both final states. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Value]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {query : Value} {before after : Physical} {answer : Bool} {memo saved : Memo}
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
      have checked := SourceCurrentConjunctionDecision.Decision.verified actual ready available formulas solver
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

/-- A valid initial memo derives a completed call and its final invariant without a supplied body trace. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Value]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memo : Memo) (query : Value) (before : Physical)
    (ready : Ready before) (available : Available before.heap query) (correct : Correct formulas solver before.heap memo) :
    ∃ answer after saved, Call budget memo query before answer after saved ∧ Effects before after ∧
      Correct formulas solver after.heap saved ∧ AnswerSound formulas solver query answer ∧ Extends memo saved := by
  obtain ⟨answer, after, actualMemo, actual, _⟩ := complete budget memo query before ready available
  exact ⟨answer, after, actualMemo, actual, verified formulas solver actual ready available correct⟩

end MicroCFTA.SourceCurrentConjunctionMemo
