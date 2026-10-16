import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEntries
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCapacity

/-!
# Numeric plans and admission for reached ordinary outer entries

The plan contains only numeric parent capacity at actual reached entries.
Admission records the current inventory and global bundle separately.
It does not require a result or a completed enclosing call.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Entry Step Reach)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Each reached parent entry has numeric capacity before that parent executes. -/
def Plan (bits budget : Nat) (root : Entry (bits + 2)) : Prop :=
  ∀ request before, Reach budget root (.edgeBody request before) →
    SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget request before

/-- A reached control inherits the numeric plan by literal path composition. -/
theorem Plan.restrict {bits budget : Nat} {root entry : Entry (bits + 2)}
    (plan : Plan bits budget root) (reached : Reach budget root entry) : Plan bits budget entry := by
  intro request before later
  exact plan request before (.trans reached later)

/-- The current parent uses its own numeric capacity entry. -/
theorem Plan.edge_body_capacity {bits budget : Nat} {request : EdgeRequest} {before : Caller (bits + 2)}
    (plan : Plan bits budget (.edgeBody request before)) :
    SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget request before :=
  plan request before .refl

/-- An evaluating edge selects its captured owner before that owner's body executes. -/
theorem Plan.edge_call_capacity {bits budget : Nat} {request : EdgeRequest} {before : Caller (bits + 2)}
    (plan : Plan bits budget (.edgeCall request before)) :
    SourceCurrentAllocatedFiniteOrdinaryParentCapacity.CallCapacity bits budget request before := by
  intro handle owner running started
  exact plan owner running (.direct (.edge_evaluate started))

/-- Current admission retains the exact operands for each of the eight entry controls. -/
def Admitted (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {width : Nat} : Entry width → Prop
  | .nodeCall request before | .nodeBody request before =>
      ∃ inventory memos, Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints request.inherited ∧
        Available before.checked.native.machine.heap request.value ∧ DNode request.value
  | .edgeCall request before | .edgeBody request before =>
      ∃ inventory memos, Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints request.inherited ∧
        EdgeResident before.checked.native.machine.heap request.value ∧ DEdge request.value
  | .rows inherited edges before =>
      ∃ inventory memos, Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints inherited ∧
        Edges before.checked.native.machine.heap edges ∧ DRows edges
  | .descendants inherited edge before =>
      ∃ inventory memos, Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints inherited ∧
        EdgeResident before.checked.native.machine.heap edge ∧ DEdge edge
  | .children combined values before | .walk combined _ values before =>
      ∃ inventory memos, Context formulas solver inventory before memos ∧ Stored before ∧
        EqReady before.checked.operations.constraints combined ∧
        Values before.checked.native.machine.heap values ∧ DChildren values

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries
