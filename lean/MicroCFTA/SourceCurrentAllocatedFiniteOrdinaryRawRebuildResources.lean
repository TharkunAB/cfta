import MicroCFTA.SourceCurrentAllocatedRawRebuild
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputStored
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCapacity

/-!
# Constructor resources for raw outer reconstruction

An edge rebuild uses the original full field and the returned children.
An ordinary node compares the returned row identities before construction.
Both steps retain their complete physical receipts and native certificates.
Initial headroom pays for their actual Work requests, including cache hits.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape RowsShape EdgeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (observe nodeRequests edgeRequests)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "rawEdge" => SourceCurrentAllocatedRawRebuild.edge
local notation "rawModify" => SourceCurrentAllocatedRawRebuild.modify
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem certificates
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before after : Checked width}
    (receipt : SourceCurrentAllocatedRawRebuild.Receipt formulas solver inventory before after)
    (native : NativeStored before.native) (output : OutputStored before.native) :
    NativeStored after.native ∧ OutputStored after.native := by
  exact ⟨⟨by simpa only [receipt.nodes] using native.nodes,
      by simpa only [receipt.edges] using native.edges⟩,
    ⟨by simpa only [receipt.nodes] using output.nodes,
      by simpa only [receipt.edges] using output.edges⟩⟩

/-- The actual descendant edge rebuild retains its field and pays for one edge request. -/
theorem edge (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (ready : Ready before) (admitted : At formulas solver inventory before)
    (resident : EdgeResident before.native.machine.heap original) (available : Values before.native.machine.heap children)
    (same : children.length = original.children.length) (native : NativeStored before.native) (output : OutputStored before.native)
    (rows arity : Nat) (profile : ChildrenShape rows arity children) (lengthBound : children.length ≤ arity)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + 1 ≤ 2 ^ (bits + 2)) :
    let result := (rawEdge original children before).1
    let after := (rawEdge original children before).2
    ∃ requests,
      SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver inventory original children before result after ∧
      NativeStored after.native ∧ OutputStored after.native ∧ EdgeShape rows arity result ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 1 ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  have receipt := SourceCurrentAllocatedRawRebuild.edge_verified formulas solver inventory original children before
    ready admitted resident available same
  have retained := certificates receipt.toReceipt native output
  have facts := ready.semantic.ready.semantic.1.normal.facts
  have produced := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeEdge
    original.entry.key.symbol original.entry.key.constraint children before.native.machine.heap
    facts.coherent facts.cached available profile lengthBound
  let requests := observe (makeEdge original.entry.key.symbol original.entry.key.constraint children) before.native.machine.heap
  have trace : Trace before.native.machine.heap (rawEdge original children before).2.native.machine.heap requests := .work _ _
  have counts : nodeRequests requests = 0 ∧ edgeRequests requests = 1 := by
    simp [requests, SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_observe, nodeRequests, edgeRequests]
  have supply := trace.next_le
  have exactSupply := trace.next_exact
  have noNodes : (rawEdge original children before).2.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next := by
    have bounded := SourceCurrentAllocatedFiniteOrdinaryReservations.reservations_le_requests requests
    omega
  exact ⟨requests, receipt, retained.1, retained.2, produced, trace, counts.1, counts.2,
    ⟨by omega, by omega⟩, noNodes, by omega⟩

/-- The actual ordered-identity branch determines all ordinary node constructor requests. -/
def modifyRequests (oldRows newRows : List (EdgeValue Symbol Guard))
    (before : Checked width) : List (SourceCurrentAllocatedFiniteOrdinaryReservations.Request Symbol Guard) :=
  if newRows.map (fun edge => edge.entry.identity) = oldRows.map (fun edge => edge.entry.identity) then []
  else observe (makeNode newRows) before.native.machine.heap

/-- Unchanged row identities emit no request; changed identities emit at most one node request. -/
theorem modify_work (original : Value Symbol Guard) (oldRows newRows : List (EdgeValue Symbol Guard))
    (before : Checked width) :
    Trace before.native.machine.heap (rawModify original oldRows newRows before).2.native.machine.heap
      (modifyRequests oldRows newRows before) ∧
      nodeRequests (modifyRequests oldRows newRows before) ≤ 1 ∧
      edgeRequests (modifyRequests oldRows newRows before) = 0 := by
  by_cases same : newRows.map (fun edge => edge.entry.identity) = oldRows.map (fun edge => edge.entry.identity)
  · rw [SourceCurrentAllocatedRawRebuild.modify_unchanged original oldRows newRows before same]
    simp only [modifyRequests, same, ↓reduceIte]
    exact ⟨.refl _, Nat.zero_le _, rfl⟩
  · simp only [modifyRequests, SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify,
      same, ↓reduceIte]
    have counts := SourceCurrentAllocatedFiniteOrdinaryReservations.makeNode_requests newRows before.native.machine.heap
    exact ⟨.work _ _, by split at counts <;> omega, counts.2⟩

/-- Initial row profiles and one node of headroom construct the complete ordinary rebuild. -/
theorem modify (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (entry : Interned InternedBinderProtocol.NodeKey)
    (oldRows newRows : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (before : Checked (bits + 2)) (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Available before.native.machine.heap (.node entry oldRows depth free))
    (resident : Edges before.native.machine.heap newRows) (native : NativeStored before.native) (output : OutputStored before.native)
    (rows arity : Nat) (profile : RowsShape rows arity newRows) (lengthBound : newRows.length ≤ rows)
    (nodes : before.native.machine.heap.nodes.next + 1 ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2)) :
    let result := (rawModify (.node entry oldRows depth free) oldRows newRows before).1
    let after := (rawModify (.node entry oldRows depth free) oldRows newRows before).2
    ∃ requests,
      SourceCurrentAllocatedRawRebuild.NodeReceipt formulas solver inventory (.node entry oldRows depth free) oldRows newRows before result after ∧
      NativeStored after.native ∧ OutputStored after.native ∧ NodeShape rows arity result ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ 1 ∧ edgeRequests requests = 0 ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + 1 ∧
      after.native.machine.heap.edges.next = before.native.machine.heap.edges.next := by
  have receipt := SourceCurrentAllocatedRawRebuild.modify_verified formulas solver inventory entry oldRows newRows depth free before
    ready admitted available resident
  have retained := certificates receipt.toReceipt native output
  have facts := ready.semantic.ready.semantic.1.normal.facts
  have produced : NodeShape rows arity (rawModify (.node entry oldRows depth free) oldRows newRows before).1 := by
    by_cases same : newRows.map (fun edge => edge.entry.identity) = oldRows.map (fun edge => edge.entry.identity)
    · have oldResident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
      have equal := InternedEdgeResidency.edge_lists_equal _ facts.coherent newRows oldRows resident oldResident same
      rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same]
      change oldRows.length ≤ rows ∧ RowsShape rows arity oldRows
      rw [← equal]
      exact ⟨lengthBound, profile⟩
    · simp only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte]
      exact SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode newRows before.native.machine.heap
        facts.coherent facts.linked resident profile lengthBound
  have work := modify_work (.node entry oldRows depth free) oldRows newRows before
  have supply := work.1.next_le
  have exactSupply := work.1.next_exact
  have noEdges : (rawModify (.node entry oldRows depth free) oldRows newRows before).2.native.machine.heap.edges.next =
      before.native.machine.heap.edges.next := by
    have bounded := SourceCurrentAllocatedFiniteOrdinaryReservations.reservations_le_requests
      (modifyRequests oldRows newRows before)
    omega
  exact ⟨_, receipt, retained.1, retained.2, produced, work.1, work.2.1, work.2.2,
    ⟨by omega, by omega⟩, by omega, noEdges⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources
