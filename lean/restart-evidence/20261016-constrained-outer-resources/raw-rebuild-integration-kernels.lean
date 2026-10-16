import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentCallerResources

namespace MicroCFTA.RawOuterResourceChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState (advance)
open SourceCurrentAllocatedPartialGraph (EdgeBody Descendants Children prefixState)
open SourceCurrentAllocatedPartialSourceReads (EdgeBodyReads DescendantsReads)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (EdgeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "erase" => EqualityLeafProjectionRuntimeEmpty.erase
local notation "rawEdge" => SourceCurrentAllocatedRawRebuild.edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
private theorem erased_profile (values : List (Value Symbol Guard)) : ChildrenShape 0 1 (erase values) := by
  induction values with
  | nil => trivial
  | cons value values ih => exact ⟨True.intro, ih⟩

/-- A rejected parent and its actual contradiction descendants use two serial edge requests. -/
theorem rejected_parent_then_descendants
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} (bits budget : Nat) (original : EdgeValue Symbol Guard)
    {before : Caller (bits + 2)} {memos : EndpointMemoGateTrace.Memos}
    (initial : Context formulas solver inventory before memos)
    (test : SourceEqualityMkEdgeAllocation.contradictory original.entry.key.constraint = true)
    (profiles : Profiles before.merge) (native : NativeStored before.checked.native) (output : OutputStored before.checked.native)
    (nodes : before.checked.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + 2 ≤ 2 ^ (bits + 2)) :
    ∃ parent checked parentRequests,
      let middle := advance before checked before.fourth before.merge
      ∃ body : EdgeBody budget ⟨.contradiction, original⟩ before parent middle,
        EdgeBodyReads formulas solver body memos memos ∧
        SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver inventory ⟨.contradiction, original⟩ before parent middle memos ∧
        ∃ result after rawRequests, ∃ actual : Descendants budget .contradiction parent middle result after,
          DescendantsReads formulas solver actual memos memos ∧
          SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver inventory parent (erase parent.children)
            checked result after.checked ∧
          NativeStored after.checked.native ∧ OutputStored after.checked.native ∧ Profiles after.merge ∧
          EdgeShape 0 1 result ∧ Trace before.checked.native.machine.heap after.checked.native.machine.heap (parentRequests ++ rawRequests) ∧
          nodeRequests (parentRequests ++ rawRequests) = 0 ∧ edgeRequests (parentRequests ++ rawRequests) = 2 ∧
          Capacity bits after.checked := by
  obtain ⟨parent, checked, parentRequests, body, reads, receipt, post, _stable, parentNative, parentOutput,
    parentProfiles, parentShape, _narrowed, parentTrace, parentNodes, parentEdges, _capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentCallerResources.rejected formulas solver bits budget
      ⟨.contradiction, original⟩ initial test profiles native output 0 0 nodes (by omega)
  let middle : Caller (bits + 2) := advance before checked before.fourth before.merge
  have prefixSame : prefixState middle parent .contradiction = middle := by
    cases middle
    rfl
  have erasedLength : (erase parent.children).length = parent.children.length := List.length_map _
  have rawNodes : checked.native.machine.heap.nodes.next ≤ 2 ^ bits := by omega
  have rawEdges : checked.native.machine.heap.edges.next + 1 ≤ 2 ^ (bits + 2) := by omega
  obtain ⟨rawRequests, rawReceipt, finalNative, finalOutput, shape, rawTrace, rawNodesCount, rawEdgesCount,
    capacity, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources.edge formulas solver inventory bits parent (erase parent.children)
      checked post.context.ready post.context.admitted receipt.resident
      (SourceEqualityEmptyPropagation.erased_scope checked.native.machine.heap parent.children).1
      erasedLength parentNative parentOutput 0 1 (erased_profile parent.children)
      (by rw [erasedLength]; exact EdgeShape.arity parent parentShape) rawNodes rawEdges
  let result := (rawEdge parent (erase parent.children) checked).1
  let after := advance middle (rawEdge parent (erase parent.children) checked).2 middle.fourth middle.merge
  have children : Children budget .contradiction parent.children (prefixState middle parent .contradiction)
      (erase parent.children) middle := by
    rw [prefixSame]
    exact .contradiction
  let actual : Descendants budget .contradiction parent middle result after := .run rfl children
  have childrenReads : SourceCurrentAllocatedPartialSourceReads.ChildrenReads formulas solver children memos memos := by
    have direct : SourceCurrentAllocatedPartialSourceReads.ChildrenReads formulas solver
        (Children.contradiction (budget := budget) (values := parent.children) (before := middle)) memos memos := .contradiction
    simpa only [prefixSame] using direct
  have actualReads : DescendantsReads formulas solver actual memos memos := .run (combined := rfl) childrenReads
  have trace : Trace before.checked.native.machine.heap after.checked.native.machine.heap (parentRequests ++ rawRequests) :=
    .trans parentTrace rawTrace
  exact ⟨parent, checked, parentRequests, body, reads, receipt, result, after, rawRequests, actual, actualReads,
    rawReceipt, finalNative, finalOutput, parentProfiles, shape, trace,
    by rw [nodeRequests_append, parentNodes, rawNodesCount],
    by rw [edgeRequests_append, parentEdges, rawEdgesCount], capacity⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- The ordered-identity fast path keeps the complete checked state and makes no request. -/
theorem unchanged_no_reservation (original : Value Symbol Guard)
    (oldRows newRows : List (EdgeValue Symbol Guard)) (before : SourceEqualityNativeDemand.State width)
    (same : newRows.map (fun edge => edge.entry.identity) = oldRows.map (fun edge => edge.entry.identity)) :
    SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before = (original, before) ∧
    SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources.modifyRequests oldRows newRows before = [] := by
  exact ⟨SourceCurrentAllocatedRawRebuild.modify_unchanged original oldRows newRows before same,
    by simp only [SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources.modifyRequests, same, ↓reduceIte]⟩

end MicroCFTA.RawOuterResourceChecks

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.RawOuterResourceChecks.rejected_parent_then_descendants
#check @MicroCFTA.RawOuterResourceChecks.rejected_parent_then_descendants
#print axioms MicroCFTA.RawOuterResourceChecks.unchanged_no_reservation
#check @MicroCFTA.RawOuterResourceChecks.unchanged_no_reservation
