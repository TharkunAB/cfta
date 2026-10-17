import MicroCFTA.SourceCurrentAllocatedPartialConditionalDomain
import MicroCFTA.SourceCurrentAllocatedParentPlain
import MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion

/-!
# Conditional shape at the actual completed parent return

Empty own equalities suffice for the parent shape law. Other children can
contain constraints. Stable execution identifies the supplied actual body
with the independently constructed plain-parent return. This is a
preservation result. It does not assert general outer completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConditionalParentShape
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Shape)
open SourceCurrentAllocatedPartialConditionalDomain (OwnEmpty Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width budget : Nat}

/-- A completed parent with empty own equalities has its exact three-way child shape. -/
theorem shape [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {request : EdgeRequest} {before after : Caller width}
    {memos : Memos} {result : EdgeValue Symbol Guard}
    (actual : EdgeBody budget request before result after)
    (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (own : OwnEmpty request.value) : Shape request.value result := by
  obtain ⟨g, s, r, e, p, h, m, c, n, stable⟩ :=
    SourceCurrentAllocatedParentWorkerCompletion.edgeBody_complete actual
  exact (SourceCurrentAllocatedParentPlain.done_shape formulas solver initial inherited resident
    (fun _ => own) (stable g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))).1

/-- Every actual parent body retains all earlier conditional outer certificates. -/
theorem stored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {request : EdgeRequest} {before after : Caller width} {result : EdgeValue Symbol Guard}
    (actual : EdgeBody budget request before result after) (previous : Stored before) : Stored after := by
  cases actual with
  | parent _ _ => exact previous.advance _ _ _

end MicroCFTA.SourceCurrentAllocatedPartialConditionalParentShape
