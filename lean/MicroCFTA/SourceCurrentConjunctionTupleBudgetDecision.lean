import MicroCFTA.SourceCurrentConjunctionTupleBudgetCompletion
import MicroCFTA.SourceCurrentConjunctionTupleBudgetSoundness

/-!
# Completed tuple-budget exploration and the public empty verdict

The actual finite table bounds the fixed-point comparisons.
The proof does not bound the table length by the tuple budget.
The public closed guard and literal possibility test give the verdict.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleBudget
open Language (Term All₂)
open SourceCurrentConjunctionEmptinessRows
open SourceCurrentConjunctionEmptinessTable (Entry)
variable {Node Symbol : Type}

/-- Finite exploration derives a completed literal fixed-point loop. -/
theorem complete [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (edges : Node → List (Edge Node Symbol)) (project : List Node → EqualityNormalize.Path → Node)
    (budget : Nat) (table : List (Entry Node)) (pending : List (List Node)) :
    ∃ final, Run empty key closed edges project budget table pending final ∧
      SourceCurrentConjunctionEmptinessTable.grow empty key closed final (final.length + 1) (fun _ => false) =
        some (ConservativeEmptiness.possible (SourceCurrentConjunctionEmptinessTable.states key final)
          (SourceCurrentConjunctionEmptinessTable.rows empty key closed final)) := by
  obtain ⟨final, actual⟩ := run_complete empty key closed edges project budget table pending
  refine ⟨final, actual, ?_⟩
  exact SourceCurrentConjunctionEmptinessTable.grow_rounds_complete empty key closed final final.length 0
    (by omega)

/-- The completed public verdict excludes every accepted finite term. -/
theorem Run.answer_sound [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (edges : Node → List (Edge Node Symbol))
    (expose : ∀ node term, meaning node term → ∃ edge ∈ edges node, EdgeAccepts meaning edge term)
    (project : List Node → EqualityNormalize.Path → Node)
    (projectLaw : ∀ children symbol terms path part, path ≠ [] → All₂ meaning children terms →
      (Term.node symbol terms).atPath path = some part → meaning (project children path) part)
    (faithful : SourceCurrentConjunctionEmptinessTable.KeyFaithful empty key closed)
    (budget : Nat) (start : Node) (final : List (Entry Node))
    (actual : Run empty key closed edges project budget [] [[start]] final)
    (verdict : SourceCurrentConjunctionEmptinessTable.answer empty key closed final
      (ConservativeEmptiness.possible (SourceCurrentConjunctionEmptinessTable.states key final)
        (SourceCurrentConjunctionEmptinessTable.rows empty key closed final)) start = true) :
    ∀ term, ¬meaning start term := by
  apply actual.sound empty key closed meaning emptyFalse edges expose project projectLaw faithful budget start final
  have rejected := (Bool.and_eq_true_iff.mp verdict).2
  simpa only [SourceCurrentConjunctionEmptinessTable.provablyEmpty,
    ConservativeEmptiness.provablyEmpty, SourceCurrentConjunctionEmptinessTable.canAccept_agrees] using rejected

end MicroCFTA.SourceCurrentConjunctionTupleBudget
