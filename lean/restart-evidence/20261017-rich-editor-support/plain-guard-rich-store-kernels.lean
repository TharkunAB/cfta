import MicroCFTA.SourceCurrentConstrainedCapRichStoreEffects

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.RichStoreEffectsKernels
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Plain" => fun guard : Guard => SourceMemoGate.plain guard = true
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapSharedSupport.Stored
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : Heap} {before : SharedState width}

/-- A full raw guard can remain above hereditary children through two exact constructor returns. -/
theorem raw_guard_then_node
    (ready : Ready formulas solver inventory record originals base before) (stored : Stored record originals before)
    (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations guard)
    (available : Values before.checked.native.machine.heap children)
    (annotated : ∀ value ∈ children, SourceEqualityAnnotationLanguage.Annotated Plain value) :
    let edge := run (makeEdge symbol guard children) before.checked.native.machine.heap
    let middle := advanceHeap before edge.2
    let node := run (makeNode [edge.1]) middle.checked.native.machine.heap
    let after := advanceHeap middle node.2
    Stored record originals after ∧ Ready formulas solver inventory record originals base after ∧
      SourceCurrentConstrainedCap.Cap Plain 1 node.1 ∧ edge.1.entry.key.constraint = guard ∧
      after.targets = before.targets ∧ after.memo = before.memo := by
  dsimp only
  let edge := run (makeEdge symbol guard children) before.checked.native.machine.heap
  let middle := advanceHeap before edge.2
  let node := run (makeNode [edge.1]) middle.checked.native.machine.heap
  let after := advanceHeap middle node.2
  have first := SourceCurrentConstrainedCapRichStoreEffects.edge ready symbol guard children field available stored
  have facts := ready.checked.semantic.ready.semantic.1.normal.facts
  have edgeCap : SourceCurrentConstrainedCap.Edge Plain 1 edge.1 :=
    SourceCurrentConstrainedCap.makeEdge Plain 1 symbol guard children _ facts.coherent facts.cached available
      (by omega) (fun child member => .plain 0 (annotated child member))
  have resident : Edges middle.checked.native.machine.heap [edge.1] := by
    intro result member
    exact (List.mem_singleton.mp member) ▸ first.2.2.2.1
  have second := SourceCurrentConstrainedCapRichStoreEffects.node first.2.1 [edge.1] resident first.1
  have middleFacts := first.2.1.checked.semantic.ready.semantic.1.normal.facts
  have nodeCap := SourceCurrentConstrainedCap.makeNode Plain 1 [edge.1] middle.checked.native.machine.heap
    middleFacts.coherent middleFacts.linked resident (by intro result member; exact (List.mem_singleton.mp member) ▸ edgeCap)
  have key := InternedOrdinaryAbsenceReplay.makeEdge_key symbol guard children _ facts.coherent
  exact ⟨second.1, second.2.1, nodeCap, congrArg EdgeKey.constraint key, rfl, rfl⟩

/-- Initial cap facts construct their own finite head, then rich stores survive its actual node rebuild. -/
theorem own_head_then_node
    (ready : Ready formulas solver inventory record originals base before) (stored : Stored record originals before)
    (depth : Nat) (input : Value Symbol Guard) (available : Available before.checked.native.machine.heap input)
    (closed : input.free = []) (bounded : SourceCurrentConstrainedCap.Cap Plain depth input) :
    ∃ exposed heap,
      SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap ∧
      let middle := advanceHeap before heap
      let result := run (makeNode (InternedEdgeResidency.nodeEdges exposed)) heap
      Stored record originals (advanceHeap middle result.2) ∧
      Ready formulas solver inventory record originals base (advanceHeap middle result.2) ∧
      SourceCurrentConstrainedCap.Cap Plain depth exposed ∧
      SourceCurrentConstrainedCapRequiredSupport.Preserves Plain input exposed ∧
      SourceCurrentConstrainedCap.Cap Plain depth result.1 ∧
      (advanceHeap middle result.2).targets = before.targets ∧ (advanceHeap middle result.2).memo = before.memo := by
  obtain ⟨exposed, heap, actual, _keeps, _available, _closed, _ordinary⟩ :=
    SourceEqualityRequiredHead.complete input before.checked.native.machine.heap ready.checked.semantic.ready available closed
  have head := SourceCurrentConstrainedCapRichStoreEffects.head depth ready actual available closed bounded stored
  let middle := advanceHeap before heap
  have facts := head.2.1.checked.semantic.ready.semantic.1.normal.facts
  have resident : Edges heap (InternedEdgeResidency.nodeEdges exposed) :=
    InternedEdgeResidency.resident_edges heap facts.linked exposed head.2.2.2.1.resident
  have next := SourceCurrentConstrainedCapRichStoreEffects.node head.2.1 (InternedEdgeResidency.nodeEdges exposed) resident head.1
  have cap := SourceCurrentConstrainedCap.makeNode Plain depth (InternedEdgeResidency.nodeEdges exposed) heap
    facts.coherent facts.linked resident (fun edge member => SourceCurrentConstrainedCap.node_edge head.2.2.2.2.1 edge member)
  exact ⟨exposed, heap, actual, next.1, next.2.1, head.2.2.2.2.1, head.2.2.2.2.2, cap, rfl, rfl⟩

#print axioms raw_guard_then_node
#check @raw_guard_then_node
#print axioms own_head_then_node
#check @own_head_then_node
end MicroCFTA.RichStoreEffectsKernels
