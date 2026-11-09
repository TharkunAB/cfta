import MicroCFTA.SourceCurrentConjunctionSharedWorklistCompletion
import MicroCFTA.SourceCurrentConjunctionSharedWorkerStability

/-!
# Initial-state completion of the actual shared call

Current readiness and query availability derive a finite successful call.
All larger observation bounds return the same answer, complete private state
and fourth memo. The proof derives the exploration, table read and fixed
point. It supplies no future success or resource forecast. The original
algorithmic tuple budget stays fixed. Numeric capacity and complete source
enumeration remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerCompletion
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorker (Outcome)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "closed" => SourceCurrentConjunctionWorklist.closed
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem decision_exists (budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    ∃ p h answer after,
      SourceCurrentConjunctionSharedWorker.decision p h budget start before = .done answer after := by
  cases classified : closed start with
  | false =>
      exact ⟨0, 0, false, SourceCurrentConjunctionSharedWorklistStep.initial budget start before,
        SourceCurrentConjunctionSharedWorker.decision_open 0 0 budget start before classified⟩
  | true =>
      obtain ⟨p, h, after, stable⟩ :=
        SourceCurrentConjunctionSharedWorklistCompletion.explore_initial budget start before ready available
      have explored := stable p h (Nat.le_refl _) (Nat.le_refl _)
      obtain ⟨table, read⟩ :=
        SourceCurrentConjunctionSharedWorker.endpoint_materializable p h budget start before after explored
      have grown := SourceCurrentConjunctionEmptinessTable.grow_rounds_complete .empty key closed
        table table.length 0 (by omega)
      exact ⟨p, h, _, after, SourceCurrentConjunctionSharedWorker.decision_closed_done
        p h budget start before after table _ classified explored read grown⟩

/-- Current readiness derives one successful decision and the same entire result at all larger bounds. -/
theorem decision_initial (budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    ∃ p h answer after, ∀ P H, p ≤ P → h ≤ H →
      SourceCurrentConjunctionSharedWorker.decision P H budget start before = .done answer after := by
  obtain ⟨p, h, answer, after, actual⟩ := decision_exists budget start before ready available
  exact ⟨p, h, answer, after, fun _ _ enoughP enoughH =>
    SourceCurrentConjunctionSharedWorkerStability.decision_done_stable actual enoughP enoughH⟩

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Initial readiness derives the same successful actual call, private state and saved memo at all larger bounds. -/
theorem call_initial [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (budget : Nat) (memo : Memo) (query : ConcreteNode) (before : ConcretePhysical)
    (ready : Ready before) (available : Available before.heap query) :
    ∃ p h answer saved after, ∀ P H, p ≤ P → h ≤ H →
      SourceCurrentConjunctionSharedWorker.call P H budget memo query before = .done (answer, saved) after := by
  cases found : memo query.referenceOf with
  | some entry =>
      obtain ⟨original, answer⟩ := entry
      refine ⟨0, 0, answer, memo, SourceCurrentConjunctionSharedWorklistStep.initial budget query before, ?_⟩
      intro P H _ _
      exact SourceCurrentConjunctionSharedWorker.call_hit P H budget memo query original before answer found
  | none =>
      obtain ⟨p, h, answer, after, stable⟩ := decision_initial budget query before ready available
      refine ⟨p, h, answer, SourceCurrentEmptinessMemo.insert memo query answer, after, ?_⟩
      intro P H enoughP enoughH
      exact SourceCurrentConjunctionSharedWorker.call_done P H budget memo query before after answer found
        (stable P H enoughP enoughH)

end MicroCFTA.SourceCurrentConjunctionSharedWorkerCompletion
