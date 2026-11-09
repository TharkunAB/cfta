import MicroCFTA.SourceCurrentConjunctionSharedWorker
import MicroCFTA.SourceCurrentConjunctionSharedWorklistValues

/-!
# Actual physical effects at the shared decision boundary

Pure table reading, fixed-point growth, and memo publication retain the
actual exploration snapshot. Open queries and memo hits retain the initial
physical state. Current readiness and query availability supply all physical
and stored-value invariants, including every failed outcome. These laws do
not assert Boolean soundness or select this worker in a checked caller.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionSharedWorker (Outcome decision)
open SourceCurrentConjunctionSharedWorklistValues (Invariant)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "initial" => SourceCurrentConjunctionSharedWorklistStep.initial
local notation "explore" => SourceCurrentConjunctionSharedWorklistRun.explore
local notation "closed" => SourceCurrentConjunctionWorklist.closed
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)

section Generic
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Pure decision stages preserve the exact actual shared exploration snapshot. -/
theorem decision_state (p h budget : Nat) (start : Node) (before : Physical) :
    (decision p h budget start before).state =
      if closed start then (explore p h budget start before).state else initial budget start before := by
  cases closedInput : closed start with
  | false => simp only [decision, closedInput, Bool.false_eq_true, ite_false, Outcome.state]
  | true =>
      simp only [decision, closedInput, ite_true]
      cases actual : explore p h budget start before with
      | failed fault after => rfl
      | done event after =>
          dsimp only [SourceCurrentConjunctionSharedWorklistStep.Outcome.state]
          cases read : SourceCurrentConjunctionSharedWorklistMaterialization.readTable
              (SourceCurrentConjunctionSharedWorker.endpointCredits p h budget start before) after with
          | none => rfl
          | some table =>
              dsimp only
              cases grown : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table
                  (table.length + 1) (fun _ => false) <;> rfl

/-- Every decision outcome derives physical effects and stored-value invariants from current inputs. -/
theorem decision_effects (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    Effects before (decision p h budget start before).state.storage.requirements.physical ∧
      Invariant (decision p h budget start before).state := by
  cases closedInput : closed start with
  | false =>
      simpa only [decision_state, closedInput, Bool.false_eq_true, ite_false,
        SourceCurrentConjunctionSharedWorklistStep.initial,
        SourceCurrentConjunctionRequirementRows.initial,
        SourceCurrentConjunctionRequirementCells.initial] using
        And.intro (Effects.refl before ready)
          (SourceCurrentConjunctionSharedWorklistValues.initial_values budget start before ready available)
  | true =>
      simpa only [decision_state, closedInput, ite_true] using
        SourceCurrentConjunctionSharedWorklistValues.explore_values p h budget start before ready available
end Generic

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq ConcreteNode]

/-- Memo handling preserves the exact selected decision snapshot or the read-free initial state. -/
theorem call_state (p h budget : Nat) (memo : Memo) (query : ConcreteNode) (before : ConcretePhysical) :
    (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state =
      match memo query.referenceOf with
      | some _ => initial budget query before
      | none => (decision p h budget query before).state := by
  cases hit : memo query.referenceOf with
  | some saved => simp only [SourceCurrentConjunctionSharedWorker.call, hit, Outcome.state]
  | none =>
      simp only [SourceCurrentConjunctionSharedWorker.call, hit]
      cases actual : decision p h budget query before <;> rfl

/-- Successful and failed memo calls retain readiness and all current stored values. -/
theorem call_effects (p h budget : Nat) (memo : Memo) (query : ConcreteNode) (before : ConcretePhysical)
    (ready : Ready before) (available : Available before.heap query) :
    Effects before (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state.storage.requirements.physical ∧
      Invariant (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state := by
  cases hit : memo query.referenceOf with
  | some saved =>
      simpa only [call_state, hit, SourceCurrentConjunctionSharedWorklistStep.initial,
        SourceCurrentConjunctionRequirementRows.initial,
        SourceCurrentConjunctionRequirementCells.initial] using And.intro (Effects.refl before ready)
        (SourceCurrentConjunctionSharedWorklistValues.initial_values budget query before ready available)
  | none => simpa only [call_state, hit] using decision_effects p h budget query before ready available

end MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
