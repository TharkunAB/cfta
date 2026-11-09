import MicroCFTA.SourceCurrentConjunctionSharedWorklistNumeric
import MicroCFTA.SourceCurrentConjunctionSharedWorkerCompletion

/-!
# Computed bounds for complete shared decisions and calls

The original heap profile and fixed tuple budget determine both observation
ceilings and the final resource profile. Each completed decision uses its
actual cached table and fixed point. Larger bounds retain the same answer,
private snapshot, and completed memo. Open decisions and memo hits retain
the initial profile. Native word capacity and total runtime are separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerNumeric
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorklistResourceControl (Profile seed)
open SourceCurrentMemoMergeResourceControl (Fits)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "closed" => SourceCurrentConjunctionWorklist.closed

/-- The original fixed-vector schedule bounds the complete private and physical result. -/
noncomputable def forecast (alphabet : List Guard) (budget resource : Nat) : Nat :=
  SourceCurrentConjunctionSharedWorklistNumeric.forecast alphabet budget resource

/-- One computed projection ceiling covers every actually reached shared force. -/
noncomputable def projectionFuel (alphabet : List Guard) (budget resource : Nat) : Nat :=
  SourceCurrentConjunctionSharedWorklistNumeric.projectionFuel alphabet budget resource

/-- One computed reader ceiling covers every actually reached native read. -/
noncomputable def readerFuel (alphabet : List Guard) (budget resource : Nat) : Nat :=
  SourceCurrentConjunctionSharedWorklistNumeric.readerFuel alphabet budget resource

/-- The final profile retains the full initial seed, including the budget and initial queue. -/
theorem forecast_ge (alphabet : List Guard) (budget resource : Nat) :
    seed budget resource ≤ forecast alphabet budget resource :=
  SourceCurrentConjunctionSharedWorklistNumeric.forecast_ge alphabet budget resource

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Current inputs derive a complete decision at the explicit ceilings and every larger pair. -/
theorem decision_initial (budget : Nat) (start : Node) (before : Physical) (resource : Nat)
    (ready : Ready before) (available : Available before.heap start) (fits : Fits resource before.heap) :
    ∃ answer after,
      (∀ P H, projectionFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource ≤ P →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource ≤ H →
        SourceCurrentConjunctionSharedWorker.decision P H budget start before = .done answer after) ∧
      Profile (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource) after := by
  cases classified : closed start with
  | false =>
      refine ⟨false, SourceCurrentConjunctionSharedWorklistStep.initial budget start before, ?_, ?_⟩
      · intro P H _ _
        exact SourceCurrentConjunctionSharedWorker.decision_open P H budget start before classified
      · exact (SourceCurrentConjunctionSharedWorklistResourceControl.initial_profile
          budget start before resource fits).mono (forecast_ge _ budget resource)
  | true =>
      obtain ⟨after, stable, profile⟩ :=
        SourceCurrentConjunctionSharedWorklistNumeric.explore_initial budget start before resource ready available fits
      let p := projectionFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource
      let h := readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource
      have explored := stable p h (Nat.le_refl _) (Nat.le_refl _)
      obtain ⟨table, read⟩ :=
        SourceCurrentConjunctionSharedWorker.endpoint_materializable p h budget start before after explored
      have grown := SourceCurrentConjunctionEmptinessTable.grow_rounds_complete .empty key closed
        table table.length 0 (by omega)
      have actual := SourceCurrentConjunctionSharedWorker.decision_closed_done p h budget start before after
        table _ classified explored read grown
      let known := ConservativeEmptiness.possible
        (SourceCurrentConjunctionEmptinessTable.states key table)
        (SourceCurrentConjunctionEmptinessTable.rows .empty key closed table)
      let answer := SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start
      refine ⟨answer, after, ?_, profile⟩
      intro P H enoughP enoughH
      exact SourceCurrentConjunctionSharedWorkerStability.decision_done_stable actual enoughP enoughH

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Current inputs derive the same complete call, private snapshot and saved memo above computed bounds. -/
theorem call_initial [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (budget : Nat) (memo : Memo) (query : ConcreteNode)
    (before : ConcretePhysical) (resource : Nat) (ready : Ready before)
    (available : Available before.heap query) (fits : Fits resource before.heap) :
    ∃ answer saved after,
      (∀ P H, projectionFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource ≤ P →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource ≤ H →
        SourceCurrentConjunctionSharedWorker.call P H budget memo query before = .done (answer, saved) after) ∧
      Profile (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource) after := by
  cases found : memo query.referenceOf with
  | some entry =>
      obtain ⟨original, answer⟩ := entry
      refine ⟨answer, memo, SourceCurrentConjunctionSharedWorklistStep.initial budget query before, ?_, ?_⟩
      · intro P H _ _
        exact SourceCurrentConjunctionSharedWorker.call_hit P H budget memo query original before answer found
      · exact (SourceCurrentConjunctionSharedWorklistResourceControl.initial_profile
          budget query before resource fits).mono (forecast_ge _ budget resource)
  | none =>
      obtain ⟨answer, after, stable, profile⟩ := decision_initial budget query before resource ready available fits
      refine ⟨answer, SourceCurrentEmptinessMemo.insert memo query answer, after, ?_, profile⟩
      intro P H enoughP enoughH
      exact SourceCurrentConjunctionSharedWorker.call_done P H budget memo query before after answer found
        (stable P H enoughP enoughH)

end MicroCFTA.SourceCurrentConjunctionSharedWorkerNumeric
