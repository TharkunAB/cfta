import MicroCFTA.SourceInternedIntersectionDispatchKeys
import MicroCFTA.SourceInternedRowsValidated
import MicroCFTA.SourceRowsMinimumPublic

/-!
# Shared-row exposure from actual physical constructor records

The reader uses the issued identity map and the canonical node payload map.
It copies each ordinary edge's symbol, constraint, and ordered children.
Only EmptyNode and ordinary nodes are interpreted here. Plain available
roots keep every reachable read inside that fragment.
-/
namespace MicroCFTA.SourcePhysicalSharedRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency InternedFreshProbeKeys
open SourceInternedIntersectionRows

/-- EmptyNode has no nonempty identity. Ordinary nodes retain their exact source identity. -/
def reference : Value Symbol Unit → SourceInternedRows.Ref
  | .node entry .. => some entry.identity
  | _ => none

/-- The explicit shared state keeps EmptyState separate from every allocated identity. -/
def encode (value : Value Symbol Unit) : SourceInternedRows.State := SourceInternedRows.stateOf (reference value)

/-- Read the canonical payload associated with an issued identity's structural key. -/
def read (state : State Symbol Unit) (identity : Nat) : Option (Value Symbol Unit) :=
  (state.nodes.issued identity).bind state.nodeRecords

/-- Copy the exact complete edge payload into the shared adapter's row representation. -/
def exposure (edge : EdgeValue Symbol Unit) : SourceInternedRows.Row Symbol Unit :=
  ⟨edge.entry.key.symbol, edge.children.map reference, edge.entry.key.constraint⟩

/-- Actual physical maps supply each ordinary identity's exposed row list. -/
def heap (state : State Symbol Unit) : SourceInternedRows.Heap Symbol Unit :=
  fun identity => ((read state identity).toList.flatMap nodeEdges).map exposure

/-- Every successful physical read returns an available complete record. -/
theorem read_available (state : State Symbol Unit) (facts : Facts state) (identity : Nat) (value : Value Symbol Unit)
    (found : read state identity = some value) : Available state value := by
  obtain ⟨key, issued, stored⟩ := Option.bind_eq_some_iff.mp found
  exact facts.cached.nodes key value stored

/-- An available ordinary record is read back under its own exact canonical identity. -/
theorem read_node (state : State Symbol Unit) (facts : Facts state)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Unit))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available state (.node entry edges depth free)) :
    read state entry.identity = some (.node entry edges depth free) := by
  have stored := resident_entry state facts.coherent _ available.resident entry rfl
  have issued := (facts.coherent.valid.2.2 entry.key entry stored).2
  simp only [read, issued, Option.bind_some]
  exact available.resident entry rfl

/-- Ordered exposure follows the actual parent record without a copied-row premise. -/
theorem heap_node (state : State Symbol Unit) (facts : Facts state)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Unit))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available state (.node entry edges depth free)) :
    heap state entry.identity = edges.map exposure := by
  simp only [heap, read_node state facts entry edges depth free available, Option.toList_some,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, nodeEdges]

/-- Every actual outgoing child retains availability in the same physical state. -/
theorem child_available (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (edge : EdgeValue Symbol Unit) (member : edge ∈ nodeEdges value)
    (child : Value Symbol Unit) (inside : child ∈ edge.children) : Available state child :=
  facts.cached.edges edge.entry.key edge (resident_edges state facts.linked value available.resident edge member) child inside

/-- A nonempty child reference lies below the actual issued-node counter. -/
theorem reference_bounded (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (identity : Nat) (same : reference value = some identity) : identity < state.nodes.next := by
  cases value <;> simp only [reference] at same <;> try contradiction
  case node entry edges depth free =>
    have equal := Option.some.inj same
    subst identity
    exact IntersectionFlatMemoKeyPhysical.entry_bounded state facts _ available entry rfl

/-- Physical issued counters give a finite closed domain for the shared traversal. -/
theorem heap_closed (state : State Symbol Unit) (facts : Facts state) :
    SourceInternedRows.ClosedDomain (heap state) (List.range state.nodes.next) := by
  intro identity _ child member
  have pending := (SourceInternedRows.mem_successors (heap state) identity child).mp member
  obtain ⟨row, present, inside⟩ := List.mem_flatMap.mp pending
  obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp present
  obtain ⟨value, valueIn, edgeIn⟩ := List.mem_flatMap.mp edgeIn
  have found : read state identity = some value := Option.mem_toList.mp valueIn
  have available := read_available state facts identity value found
  obtain ⟨childValue, childIn, same⟩ := List.mem_map.mp inside
  exact List.mem_range.mpr (reference_bounded state facts childValue
    (child_available state facts value available edge edgeIn childValue childIn) child same)

/-- Every available plain root has a stable complete shared-row traversal. -/
theorem toRows_finite (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) :
    ∃ fuel raw, ∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap state) larger (reference value) = some raw := by
  apply SourceInternedRows.toRows_finite (heap state) (List.range state.nodes.next) (heap_closed state facts)
  intro identity same
  exact List.mem_range.mpr (reference_bounded state facts value available identity same)

/-- The shared structural row is exactly the physical row with encoded child references. -/
theorem exposure_row (edge : EdgeValue Symbol Unit) :
    SourceInternedRows.interpret (fun (_ : Unit) (_ : Language.Term Symbol) => true) (SourceInternedRows.transition (exposure edge)) =
      SymbolicGraphView.renameEdge encode (row edge) := by
  simp only [SourceInternedRows.interpret, SourceInternedRows.transition, exposure, SymbolicGraphView.renameEdge, row, List.map_map]
  rfl

/-- Actual available plain readback gives exact ordered rows in the shared graph. -/
theorem graph_readback (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value) :
    SourceInternedRows.graph (heap state) (fun _ _ => true) (encode value) =
      (rows value).map (SymbolicGraphView.renameEdge encode) := by
  cases plain with
  | empty => rfl
  | node entry edges depth free children =>
      simp only [encode, reference, SourceInternedRows.stateOf, SourceInternedRows.graph, heap_node state facts entry edges depth free available,
        List.map_map, rows, nodeEdges]
      exact List.map_congr_left (fun edge _ => exposure_row edge)

end MicroCFTA.SourcePhysicalSharedRows
