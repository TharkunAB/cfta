import MicroCFTA.SourceCurrentConjunctionDecision
import MicroCFTA.SourceCurrentConjunctionWorklistSoundness
import MicroCFTA.SourceCurrentEmptinessMemo

/-!
# Conservative meaning of actual current conjunction decisions

The actual open branch retains both physical states. The closed branch
derives coverage from its actual allocated worklist and uses its completed
grow receipt. The earlier AnswerSound predicate is immutable semantic data.
No earlier Decision or memo Call is used as an execution receipt.
-/
namespace MicroCFTA.SourceCurrentConjunctionDecision
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorklist (PendingReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula

/-- Every actual current decision derives physical effects and the completed memo's semantic law. -/
theorem Decision.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {start : Value Symbol Guard} {before after : Physical} {result : Bool}
    (actual : Decision budget start before result after) (ready : Ready before)
    (available : Available before.heap start)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Effects before after ∧ SourceCurrentEmptinessMemo.AnswerSound formulas solver start result := by
  cases actual with
  | open_input _ =>
      exact ⟨Effects.refl _ ready, ⟨fun _ => rfl, by intro impossible; cases impossible⟩⟩
  | closed closedInput explored grown =>
      have pending : PendingReady before [[start]] := by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available
      have checked := explored.verified formulas solver (fun _ _ => False) ready
        (by intro entry member; cases member) pending (by intro entry member; cases member)
      refine ⟨checked.1, ?_, ?_⟩
      · intro notClosed
        exact False.elim (notClosed (List.isEmpty_iff.mp closedInput))
      · intro accepted ambient
        exact SourceCurrentConjunctionWorklistSoundness.run_answer_sound formulas solver ambient explored ready
          (by intro entry member; cases member) pending (by intro entry member; cases member)
          start available _ _ grown accepted

end MicroCFTA.SourceCurrentConjunctionDecision
