import MicroCFTA.SourceCurrentAllocatedPartialStepEffects

namespace MicroCFTA.PartialEffectsIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
local notation "rawEdge" => SourceCurrentAllocatedRawRebuild.edge
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

 theorem inherited_then_indexed
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (edge : EdgeValue Symbol Guard) (inherited payload : EqValue) (index : Nat)
    (resident : EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (actual : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some payload)) :
    SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory edge.entry.key.constraint inherited before.checked payload ∧
    SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory (prefixState before edge inherited) payload index ∧
    Post formulas solver inventory before (descend (prefixState before edge inherited) payload index).2 memos := by
  have first := SourceCurrentAllocatedPartialStepEffects.inherited_prefix formulas solver inventory before memos context
    edge inherited payload resident inheritedReady actual
  have last := SourceCurrentAllocatedPartialStepEffects.descent formulas solver inventory (prefixState before edge inherited)
    memos first.2.context payload index first.1.combinedReady
  exact ⟨first.1, last.1, first.2.trans last.2⟩

 theorem two_raw_edges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (edge : EdgeValue Symbol Guard) (firstChildren lastChildren : List (Value Symbol Guard))
    (resident : EdgeResident before.checked.native.machine.heap edge)
    (firstAvailable : Values before.checked.native.machine.heap firstChildren)
    (lastAvailable : Values before.checked.native.machine.heap lastChildren)
    (firstLength : firstChildren.length = edge.children.length) (lastLength : lastChildren.length = firstChildren.length) :
    let middle := advance before (rawEdge edge firstChildren before.checked).2 before.fourth before.merge
    let after := advance middle (rawEdge (rawEdge edge firstChildren before.checked).1 lastChildren middle.checked).2 middle.fourth middle.merge
    Post formulas solver inventory before after memos ∧
      after.merge = before.merge ∧ after.fourth = before.fourth ∧
      after.nodeResults = before.nodeResults ∧ after.edgeResults = before.edgeResults := by
  dsimp only
  have first := SourceCurrentAllocatedPartialStepEffects.raw_edge formulas solver inventory before memos context edge firstChildren
    resident firstAvailable firstLength
  let middle := advance before (rawEdge edge firstChildren before.checked).2 before.fourth before.merge
  have nextAvailable : Values middle.checked.native.machine.heap lastChildren :=
    fun value member => first.2.effects.keeps.available value (lastAvailable value member)
  have nextLength : lastChildren.length = (rawEdge edge firstChildren before.checked).1.children.length := by
    rw [first.1.children]
    exact lastLength
  have last := SourceCurrentAllocatedPartialStepEffects.raw_edge formulas solver inventory middle memos first.2.context
    (rawEdge edge firstChildren before.checked).1 lastChildren first.1.resident nextAvailable nextLength
  exact ⟨first.2.trans last.2, rfl, rfl, rfl, rfl⟩

 theorem actual_node_publication
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos) (request : NodeRequest)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) :
    Post formulas solver inventory before (beginNode request before).2.2 memos := by
  exact Post.rebase context rfl rfl rfl
    (SourceCurrentAllocatedPartialMemoSound.beginNode_sound formulas solver request before context.sound inherited available)

 theorem exact_running_node_finish
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos) (handle : Nat) (owner : NodeRequest) (result : Value Symbol Guard)
    (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (available : Available before.checked.native.machine.heap result)
    (law : SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver owner result) :
    Post formulas solver inventory before (finishNode handle result before) memos ∧
      (finishNode handle result before).nodeResults.cells handle = some ⟨owner, .returned result⟩ := by
  exact ⟨Post.rebase context rfl rfl rfl
      (SourceCurrentAllocatedPartialMemoSound.finishNode_sound formulas solver handle owner result before context.sound
        running available law), finishNode_returned handle owner result before running⟩

 theorem actual_edge_publication
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos) (request : EdgeRequest)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) :
    Post formulas solver inventory before (beginEdge request before).2.2 memos := by
  exact Post.rebase context rfl rfl rfl
    (SourceCurrentAllocatedPartialMemoSound.beginEdge_sound formulas solver request before context.sound inherited resident)

 theorem exact_running_edge_finish
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos) (handle : Nat) (owner : EdgeRequest) (result : EdgeValue Symbol Guard)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (resident : EdgeResident before.checked.native.machine.heap result)
    (law : SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver owner result) :
    Post formulas solver inventory before (finishEdge handle result before) memos ∧
      (finishEdge handle result before).edgeResults.cells handle = some ⟨owner, .returned result⟩ := by
  exact ⟨Post.rebase context rfl rfl rfl
      (SourceCurrentAllocatedPartialMemoSound.finishEdge_sound formulas solver handle owner result before context.sound
        running resident law), finishEdge_returned handle owner result before running⟩

end MicroCFTA.PartialEffectsIntegration
