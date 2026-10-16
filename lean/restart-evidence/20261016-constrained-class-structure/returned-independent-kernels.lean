import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReturned
namespace FiniteOrdinaryReturnedIndependent
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedFiniteOrdinaryReturned (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat}

/-- Literal Empty completion derives its local certificate and supports actual warm readback. -/
theorem node_finish_empty {before : State width} {handle : Nat} {owner : NodeRequest}
    (stored : Stored before) (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap owner.value)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node owner.value) :
    let after := finishNode handle .empty before
    Stored after ∧ after.edgeResults = before.edgeResults ∧ after.checked = before.checked ∧
      after.nodeResults.cells handle = some ⟨owner, .returned .empty⟩ ∧ NodeNarrow owner.value .empty := by
  let after := finishNode handle .empty before
  have final : Stored after := stored.finishNode .empty running (fun _ => ⟨.empty, Nat.zero_le _⟩)
  have returned := finishNode_returned handle owner .empty before running
  have warm := final.node_hit coherent returned available available rfl domain
  exact ⟨final, rfl, rfl, returned, warm⟩

/-- Identity edge completion derives warm structure and strict child rank at the original owner. -/
theorem edge_finish_children {before : State width} {handle : Nat} {owner : EdgeRequest}
    (stored : Stored before) (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap owner.value)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge owner.value) :
    let after := finishEdge handle owner.value before
    Stored after ∧ after.nodeResults = before.nodeResults ∧ after.checked = before.checked ∧
      EdgeNarrow owner.value owner.value ∧
      ∀ inherited child, child ∈ owner.value.children →
        SourceCurrentAllocatedFiniteOrdinaryDomain.Node child ∧
          SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨inherited, child⟩ <
            SourceCurrentAllocatedPartialActiveOrder.edgeRank owner := by
  let after := finishEdge handle owner.value before
  have final : Stored after := stored.finishEdge owner.value running (fun domain => ⟨domain, Nat.le_refl _⟩)
  have returned := finishEdge_returned handle owner owner.value before running
  have warm := final.edge_hit coherent returned resident resident rfl domain
  exact ⟨final, rfl, rfl, warm, fun inherited child member => final.child returned domain inherited child member⟩
end FiniteOrdinaryReturnedIndependent
#print axioms FiniteOrdinaryReturnedIndependent.node_finish_empty
#check @FiniteOrdinaryReturnedIndependent.node_finish_empty
#print axioms FiniteOrdinaryReturnedIndependent.edge_finish_children
#check @FiniteOrdinaryReturnedIndependent.edge_finish_children
