import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterVerification

/-!
# Strict reads for a supplied finite ordinary parent graph

Numeric capacity at the same parent entry derives its reached checks.
The supplied raw graph gives a literal successful parent execution.
Whole-return uniqueness aligns a constructed strict producer with it.
No enclosing node or caller completion is an input to this proof.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterParentReads
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedPartialMemoSound (EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial entry facts derive strict reads for that exact supplied raw parent return. -/
theorem edge_body (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : EdgeRequest} {before after : Caller (bits + 2)} {result : EdgeValue Symbol Guard}
    (actual : EdgeBody budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (capacity : SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget request before) :
    ∃ final, EdgeBodyReads formulas solver actual memos final := by
  have ranges := SourceCurrentAllocatedFiniteOrdinaryParentCapacity.resident_ranges bits formulas solver
    budget request initial inherited resident domain stored capacity
  cases actual with
  | parent field parent =>
      obtain ⟨g, s, r, e, p, h, m, c, n, stable⟩ :=
        SourceCurrentAllocatedParentWorkerCompletion.edge_complete parent field
      have done := stable g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      obtain ⟨next, final, chosen, reads, receipt, post⟩ :=
        SourceCurrentAllocatedParentWorkerActual.resident_verified formulas solver initial inherited resident ranges done
      exact ⟨final, reads⟩

/-- The same supplied parent return has its full physical, semantic, and structural receipts. -/
theorem verified (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : EdgeRequest} {before after : Caller (bits + 2)} {result : EdgeValue Symbol Guard}
    (actual : EdgeBody budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : DEdge request.value) (stored : Stored before)
    (capacity : SourceCurrentAllocatedFiniteOrdinaryParentCapacity.ParentCapacity bits budget request before) :
    ∃ final, EdgeBodyReads formulas solver actual memos final ∧ Checks (edgeBodyTrace actual) ∧
      ∃ next, Post formulas solver next before after final ∧
        EdgeResident after.checked.native.machine.heap result ∧ Stored after ∧
        EdgeNarrow request.value result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨final, reads⟩ := edge_body bits formulas solver actual inventory initial inherited resident domain stored capacity
  obtain ⟨checks, next, post, available, finalStored, narrowed, law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_body formulas solver reads inventory initial
      inherited resident domain stored
  exact ⟨final, reads, checks, next, post, available, finalStored, narrowed, law⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterParentReads
