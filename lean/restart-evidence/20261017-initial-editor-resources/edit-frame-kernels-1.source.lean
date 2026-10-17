import MicroCFTA.SourceCurrentConstrainedCapEditFrame

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.EditFrameIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapEditFrame (constructorProfile headProfile headFuel)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : Heap} {before : SharedState width}

/-- Two actual constructor requests derive the second frame and resources from the first return. -/
theorem edge_then_node (profile : Profile) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (ready : Ready formulas solver inventory record originals base before)
    (stored : Stored record originals before) (symbol : Symbol) (guard : Guard)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations guard) :
    let edgeWork := run (makeEdge symbol guard []) before.checked.native.machine.heap
    let middle := advanceHeap before edgeWork.2
    let nodeWork := run (makeNode [edgeWork.1]) edgeWork.2
    let after := advanceHeap middle nodeWork.2
    Frame formulas solver inventory after.checked ∧
      Fits (constructorProfile 1 (constructorProfile 0 profile)) after.checked ∧
      Stored record originals after ∧ Ready formulas solver inventory record originals base after ∧
      Effects (physical before.checked) (physical after.checked) ∧ Available nodeWork.2 nodeWork.1 ∧
      Cap Plain 1 nodeWork.1 ∧ after.targets = before.targets ∧ after.memo = before.memo ∧
      after.checked.operations = before.checked.operations ∧
      after.checked.native.nodes = before.checked.native.nodes ∧
      after.checked.native.edges = before.checked.native.edges ∧
      after.checked.native.machine.domains = before.checked.native.machine.domains := by
  let edgeWork := run (makeEdge symbol guard []) before.checked.native.machine.heap
  let middle := advanceHeap before edgeWork.2
  let nodeWork := run (makeNode [edgeWork.1]) edgeWork.2
  have edge := SourceCurrentConstrainedCapEditFrame.edge profile 0 frame fits ready symbol guard [] field
    (by intro value member; cases member) (Nat.le_refl _) stored
  have resident : Edges middle.checked.native.machine.heap [edgeWork.1] := by
    intro value member
    exact (List.mem_singleton.mp member) ▸ edge.2.2.2.2.2.1
  have node := SourceCurrentConstrainedCapEditFrame.node (constructorProfile 0 profile) 1
    edge.1 edge.2.1 edge.2.2.2.1 [edgeWork.1] resident (Nat.le_refl _) edge.2.2.1
  have bounded : ∀ value ∈ [edgeWork.1], SourceCurrentConstrainedCap.Edge Plain 1 value := by
    intro value member
    cases List.mem_singleton.mp member
    change ∀ child ∈ edgeWork.1.children, Cap Plain 0 child
    rw [edge.2.2.2.2.2.2]
    intro child member
    cases member
  have facts := edge.2.2.2.1.checked.good.native.machine.1
  have cap := SourceCurrentConstrainedCap.makeNode Plain 1 [edgeWork.1] edgeWork.2
    facts.coherent facts.linked resident bounded
  exact ⟨node.1, node.2.1, node.2.2.1, node.2.2.2.1,
    edge.2.2.2.2.1.trans node.2.2.2.2.1, node.2.2.2.2.2, cap, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Initial closed recursive input constructs its own Head and the exact returned frame. -/
theorem constructed_recursive_head (profile : Profile) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (ready : Ready formulas solver inventory record originals base before)
    (stored : Stored record originals before) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (available : Available before.checked.native.machine.heap (.mu entry body depth ordinary))
    (closed : (Value.mu entry body depth ordinary).free = []) :
    ∃ exposed heap,
      ∃ actual : SourceEqualityRequiredHead.Head (.mu entry body depth ordinary)
        before.checked.native.machine.heap exposed heap,
      Frame formulas solver inventory (advanceHeap before heap).checked ∧
        Fits (headProfile profile) (advanceHeap before heap).checked ∧
        Stored record originals (advanceHeap before heap) ∧
        Ready formulas solver inventory record originals base (advanceHeap before heap) ∧
        Effects (physical before.checked) (physical (advanceHeap before heap).checked) ∧
        Available heap exposed ∧ exposed.free = [] ∧ SourceEqualityRequiredCache.Ordinary exposed ∧
        SourceCurrentProjectionNumericReplay.HeadReady (headFuel profile) actual ∧
        (advanceHeap before heap).targets = before.targets ∧
        (advanceHeap before heap).memo = before.memo ∧
        (advanceHeap before heap).checked.operations = before.checked.operations := by
  obtain ⟨exposed, heap, actual, _kept, _available, resultClosed, ordinaryResult⟩ :=
    SourceEqualityRequiredHead.complete (.mu entry body depth ordinary) before.checked.native.machine.heap
      ready.checked.semantic.ready available closed
  have produced := SourceCurrentConstrainedCapEditFrame.head profile frame fits ready actual available closed stored
  exact ⟨exposed, heap, actual, produced.1, produced.2.1, produced.2.2.1, produced.2.2.2.1,
    produced.2.2.2.2.1, produced.2.2.2.2.2.1, resultClosed, ordinaryResult,
    produced.2.2.2.2.2.2.2, rfl, rfl, rfl⟩

end MicroCFTA.EditFrameIntegration

#print axioms MicroCFTA.EditFrameIntegration.edge_then_node
#check @MicroCFTA.EditFrameIntegration.edge_then_node
#print axioms MicroCFTA.EditFrameIntegration.constructed_recursive_head
#check @MicroCFTA.EditFrameIntegration.constructed_recursive_head
