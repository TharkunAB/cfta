import MicroCFTA.SourceCurrentOuterParentHistory
import MicroCFTA.SourceCurrentActualOwnerSelection

/-!
# Selected owner copies through actual warm edge requests

Current coherent physical readback identifies the complete owner value.
The returned edge's recorded writer supplies its actual Parent execution.
That same execution supplies the selected Scan, Required and pass receipts,
with false primary traces on its original forest at its final Scan heap.
The historical writer need not have the enclosing owner available at entry.
No retained same-child equality pair or outer termination is proved here.
-/
namespace MicroCFTA.SourceCurrentOuterOwnerSelection
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants (Good EdgeReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Origins" => SourceCurrentOuterParentHistory.Origins
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A same-owner reference at an actual edge return recovers its selected writer and original gates. -/
theorem selected {fuel g s r e p h m c n budget handle index : Nat}
    {request : EdgeRequest} {owner : NodeRequest} {before after : Caller width}
    {returned : Edge} {child : Node} {ownerEntry ownerDepth ownerFree}
    {ownerRows : List Edge}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done returned after)
    (good : Good before) (ready : EdgeReady before request) (origins : Origins before)
    (active : before.nodeResults.cells handle = some ⟨owner,.evaluating⟩)
    (ordinary : owner.value = .node ownerEntry ownerRows ownerDepth ownerFree)
    (member : request.value ∈ ownerRows)
    (found : returned.children[index]? = some child)
    (sameReference : child.referenceOf = owner.value.referenceOf) :
    Origins after ∧ child = owner.value ∧
    ∃ (wg ws wr we wp wh wm wc wn wbudget : Nat) (writerBefore writerAfter : Checked width)
      (writerFourth writerSaved : Fourth) (writerMemo writerMerge : Memo),
      SourceCurrentAllocatedParentWorker.edge wg ws wr we wp wh wm wc wn wbudget
        request.value.entry.key.symbol request.value.entry.key.constraint request.inherited
        request.value.children writerBefore writerFourth writerMemo =
          .done returned writerAfter writerSaved writerMerge ∧
      SourceCurrentNativeOperationHeap.Good writerBefore ∧
      SourceCurrentMemoMergeEffects.Stored writerBefore.native.machine.heap writerMemo ∧
      (SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
        FieldAvailable writerBefore.operations request.value.entry.key.constraint ∧
        EqReady writerBefore.operations.constraints request.inherited ∧
        Values writerBefore.native.machine.heap request.value.children) ∧
      ∃ (loaded : Allocated) (middle : Checked width) (records kept : List Record)
      (scanned : Checked width) (scanFourth : Fourth) (prepared : List Node) (preparedHeap : Heap),
      SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false ∧
      SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint writerBefore.operations.constraints = .ok (some loaded) ∧
      SourceCurrentAllocatedLocalWorker.reduce wg ws wr we wp wh wm wc wn wbudget loaded request.inherited request.value.children
        writerBefore writerFourth writerMemo = .done returned.children middle writerSaved writerMerge ∧
      SourceCurrentAllocatedMkEdge.build request.value.entry.key.symbol loaded returned.children middle = (.ok returned, writerAfter) ∧
      SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded)
        returned.children.length = true ∧
      (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard request.inherited writerBefore.operations).1 =
        .ok (.classes records) ∧
      SourceCurrentAllocatedRecordScanWorker.scan wg ws wp wh wn wbudget request.value.children records
        (prefixState writerBefore loaded request.inherited) writerFourth = .done (none, kept) scanned scanFourth ∧
      kept ≠ [] ∧
      SourceEqualityRequiredExecution.requireAll wr wh
        (SourceEqualitySelectedRequired.paths (kept.map SourceEqualityClassOrder.Record.paths)) request.value.children
        scanned.native.machine.heap = .done prepared preparedHeap ∧
      SourceCurrentAllocatedClassWorker.pass we wp wh wm wc wn kept prepared
        (advanceHeap scanned preparedHeap) writerMemo = .done returned.children middle writerMerge ∧
      writerSaved = scanFourth ∧
      ∀ record ∈ kept, EndpointStatefulGateTrace.ClassTrace source reaches request.value.children record.paths
        scanned.native.machine.heap false scanned.native.machine.heap := by
  obtain ⟨current,effect,resident⟩ := SourceCurrentOuterPrefixInvariants.edge_done actual good ready
  have ownerBefore := (good.nodes.checked _ _ active).1.2
  have ownerAfter := effect.keeps.available owner.value ownerBefore
  have children := current.checked.semantic.ready.semantic.1.normal.facts.cached.edges _ _ resident
  have childAfter := children child (List.mem_of_getElem? found)
  have same := SourceEqualityPartialKeyTransport.available_reference_eq _
    current.checked.heap.semantic.1.normal.facts.coherent child owner.value childAfter ownerAfter sameReference
  have exactOwner : returned.children[index]? = some (.node ownerEntry ownerRows ownerDepth ownerFree) := by
    rw [same,ordinary] at found
    exact found
  obtain ⟨retained,wg,ws,wr,we,wp,wh,wm,wc,wn,wbudget,writerBefore,writerAfter,
    writerFourth,writerSaved,writerMemo,writerMerge,written,initial,stored,live⟩ :=
    SourceCurrentOuterParentHistory.edge_call actual good ready origins
  exact ⟨retained,same,wg,ws,wr,we,wp,wh,wm,wc,wn,wbudget,writerBefore,writerAfter,
    writerFourth,writerSaved,writerMemo,writerMerge,written,initial,stored,live,
    SourceCurrentActualOwnerSelection.selected written initial stored live member exactOwner⟩

end MicroCFTA.SourceCurrentOuterOwnerSelection
