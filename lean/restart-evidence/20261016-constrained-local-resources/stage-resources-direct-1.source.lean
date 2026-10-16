import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryCallerResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScanRanges
import MicroCFTA.SourceCurrentConjunctionScanClassPassActual
import MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion

/-!
# Initial resources for Scan, Required, and the current class pass

Finite ordinary inputs derive the allocation-free selected-only Scan.
Required retains the original forest profile at its actual returned heap.
Initial cumulative headroom pays for Required and the following class pass.
Every receipt and Work trace uses these same returned states.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageResources
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open SourceCurrentConjunctionScanClassPass (Reduction Receipt)
open SourceCurrentConjunctionScanClassPassActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate

/-- Required keeps the initial row limit before the class pass starts. -/
abbrev outputRows := SourceCurrentAllocatedFiniteOrdinaryPassResources.outputRows

/-- Required keeps the initial arity limit before the class pass starts. -/
abbrev outputArity := SourceCurrentAllocatedFiniteOrdinaryPassResources.outputArity

/-- Original node occurrences pay for Required before the complete class pass. -/
def nodeBudget (records : List Record) (rows arity count depth bound : Nat) : Nat :=
  count * SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount rows arity bound +
    SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget records rows arity count depth bound

/-- Original row occurrences pay for Required before the complete class pass. -/
def edgeBudget (records : List Record) (rows arity count depth bound : Nat) : Nat :=
  count * SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount rows arity bound +
    SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget records rows arity count depth bound

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial profiles and total headroom construct the exact current successful class stage. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after saved next final requests,
    ∃ actual : Reduction budget records values before fourth memo none results after fourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next records values results before after fourth fourth memo saved none final ∧
      SourceCurrentAllocatedLocalWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n
          budget records values before fourth memo) results after fourth saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (outputRows records rows count depth bound) (outputArity records arity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget records rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget records rows arity count depth bound ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound := by
  have domain := ChildrenShape.domain values profile
  have scanRanges := SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget sourceGate sourceReaches values
    (records.map Record.paths) before fourth ready.good.native.machine.1.coherent available domain
  obtain ⟨scan, scanReads⟩ := SourceCurrentAllocatedFiniteOrdinaryScan.construct budget values
    (records.map Record.paths) before fourth ready available domain memos
  obtain ⟨kept, retained⟩ := SourceCurrentConjunctionSelectedRecords.retained_records records scan
  have sameLength : kept.length = records.length := by
    have lengths := congrArg List.length retained.fields.2
    simpa only [List.length_map] using lengths
  have sameKept := retained.fields.1.eq_of_length sameLength
  subst kept
  have pathsProper : ∀ paths ∈ records.map Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  obtain ⟨requiredValues, heap, requiredRequests, stable, _keeps, _semantic, _available, requiredProfile,
    requiredHeight, requiredLength, requiredTrace, requiredNodes, requiredEdges, requiredNodeSupply, requiredEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryCallerResources.required
      (SourceEqualitySelectedRequired.paths (records.map Record.paths)) values before.native.machine.heap ready.semantic available profile
  obtain ⟨fuel, readFuel, enough⟩ := stable
  have requiredDone := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
    formulas solver inventory scan ready admitted available pathsProper pathsActive correct scanRanges requiredDone
  obtain ⟨requiredMemos, requiredReads, requiredValid, _unfolding, _queries⟩ := SourceCurrentRequiredQueryMemos.requireAll_memos
    fuel readFuel (SourceEqualitySelectedRequired.paths (records.map Record.paths)) values requiredValues
      before.native.machine.heap heap requiredDone ready.semantic ready.costs available memos valid
  have requiredNarrow := SourceCurrentAllocatedFiniteOrdinaryRequired.requireAll_done fuel readFuel
    (SourceEqualitySelectedRequired.paths (records.map Record.paths)) values requiredValues before.native.machine.heap heap
    requiredDone ready.semantic available domain
  have currentNative : NativeStored (advanceHeap before heap).native :=
    SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored before.native _ native
  have currentOutput : OutputStored (advanceHeap before heap).native :=
    SourceCurrentAllocatedFiniteOrdinaryOutputStored.advance_stored before.native _ output
  have literalCounts := SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.children values profile bound heightBound
  have nodeCountBound : (SourceCurrentAllocatedFiniteOrdinaryOccurrences.children values).1 ≤
      count * SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount rows arity bound :=
    Nat.le_trans literalCounts.1 (Nat.mul_le_mul_right _ lengthBound)
  have edgeCountBound : (SourceCurrentAllocatedFiniteOrdinaryOccurrences.children values).2 ≤
      count * SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount rows arity bound :=
    Nat.le_trans literalCounts.2 (Nat.mul_le_mul_right _ lengthBound)
  have passNodes : (advanceHeap before heap).native.machine.heap.nodes.next +
      SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget records rows arity count depth bound ≤ 2 ^ bits := by
    change heap.nodes.next + _ ≤ _
    unfold nodeBudget at nodes
    omega
  have passEdges : (advanceHeap before heap).native.machine.heap.edges.next +
      SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2) := by
    change heap.edges.next + _ ≤ _
    unfold edgeBudget at edges
    omega
  obtain ⟨results, after, saved, _passInventory, final, passRequests, pass, passReads, _passReceipt,
    _passStable, finalNative, finalOutput, finalProfiles, produced, narrowed, sameLength, finalHeight,
    passTrace, passNodeCount, passEdgeCount, capacity, passNodeSupply, passEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryPassResources.complete formulas solver requiredInventory bits records
      (fun record member => (fields record member).1) (fun record member => (fields record member).2.2)
      requiredValues (advanceHeap before heap) memo requiredReceipt.ready requiredReceipt.admitted requiredReceipt.resident
      (physical.grows requiredReceipt.effects.keeps) profiles currentNative currentOutput covered requiredMemos requiredValid
      rows arity count depth bound requiredProfile (by omega) pathsBound
      (Nat.le_trans requiredHeight heightBound) passNodes passEdges
  have actual : Reduction budget records values before fourth memo none results after fourth saved :=
    .completed scan retained requiredDone pass
  have reads : Reads formulas solver actual memos final :=
    .completed (retained := retained) (required := requiredDone) scanReads requiredReads passReads
  obtain ⟨next, receipt⟩ := SourceCurrentConjunctionScanClassPassActual.verified formulas solver inventory reads
    ready admitted available proper fields correct physical covered scanRanges valid
  refine ⟨results, after, saved, next, final, requiredRequests ++ passRequests, actual, reads, receipt,
    SourceCurrentAllocatedLocalWorkerCompletion.classes_complete actual, finalNative, finalOutput, finalProfiles,
    produced, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_trans requiredNarrow.2.2.2.2 narrowed,
    sameLength.trans requiredLength, finalHeight, requiredTrace.trans passTrace, ?_, ?_, capacity, ?_, ?_⟩
  · rw [nodeRequests_append]
    unfold nodeBudget
    omega
  · rw [edgeRequests_append]
    unfold edgeBudget
    omega
  · change after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + _
    change after.native.machine.heap.nodes.next ≤ heap.nodes.next + _ at passNodeSupply
    unfold nodeBudget
    omega
  · change after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + _
    change after.native.machine.heap.edges.next ≤ heap.edges.next + _ at passEdgeSupply
    unfold edgeBudget
    omega

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageResources
