import MicroCFTA.SourceCurrentConjunctionSharedWorklistCellOrigins
import MicroCFTA.SourceCurrentConjunctionSharedWorker

/-!
# Derived descriptor origins at the shared caller boundary

A successful exploration derives its own descriptor-origin list. Pure table
reading and fixed-point growth retain that private snapshot. Open inputs
and memo hits retain the empty initial cell heap. These laws do not certify
an incoming memo answer or assert refinement after failed forcing.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerOrigins
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorker
open SourceCurrentConjunctionSharedWorklistCellOrigins (flatten initial_origins explore_origins)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "Refined" => SourceCurrentConjunctionRequirementCellsRefinement.Invariant
local notation "explore" => SourceCurrentConjunctionSharedWorklistRun.explore
local notation "closed" => SourceCurrentConjunctionWorklist.closed
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)

section Generic
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Original current inputs derive descriptor origins for every successful shared decision. -/
theorem decision_origins (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    match decision p h budget start before with
    | .failed _ _ => True
    | .done _ after => ∃ batches, Refined (flatten batches) after.storage.requirements := by
  cases closedInput : closed start with
  | false =>
      rw [decision_open p h budget start before closedInput]
      exact ⟨[], initial_origins budget start before⟩
  | true =>
      have origins := explore_origins p h budget start before ready available
      simp only [decision, closedInput, ite_true]
      cases actual : explore p h budget start before with
      | failed fault after => trivial
      | done event after =>
          have stored : ∃ batches, Refined (flatten batches) after.storage.requirements := by
            simpa only [actual] using origins
          dsimp only
          cases read : SourceCurrentConjunctionSharedWorklistMaterialization.readTable
              (endpointCredits p h budget start before) after with
          | none => trivial
          | some table =>
              dsimp only
              cases grown : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table
                  (table.length + 1) (fun _ => false) with
              | none => trivial
              | some known => exact stored
end Generic

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq ConcreteNode]

/-- Actual hits and successful misses derive origins without assuming memo answer correctness. -/
theorem call_origins (p h budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo)
    (query : ConcreteNode) (before : ConcretePhysical)
    (ready : Ready before) (available : Available before.heap query) :
    match SourceCurrentConjunctionSharedWorker.call p h budget memo query before with
    | .failed _ _ => True
    | .done _ after => ∃ batches, Refined (flatten batches) after.storage.requirements := by
  cases hit : memo query.referenceOf with
  | some saved =>
      simp only [SourceCurrentConjunctionSharedWorker.call, hit]
      exact ⟨[], initial_origins budget query before⟩
  | none =>
      have origins := decision_origins p h budget query before ready available
      simp only [SourceCurrentConjunctionSharedWorker.call, hit]
      cases actual : decision p h budget query before with
      | failed fault after => trivial
      | done answer after =>
          simpa only [actual, Outcome.bind] using origins

end MicroCFTA.SourceCurrentConjunctionSharedWorkerOrigins
