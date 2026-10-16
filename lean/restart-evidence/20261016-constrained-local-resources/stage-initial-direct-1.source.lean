import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageCapacity

/-!
# Initial headroom for the current Scan continuation capacity

Every earlier Scan retains the full entry state and selects every record.
Initial profiles construct Required at that unchanged heap.
Literal Required uniqueness identifies every supplied earlier return.
The remaining initial budget derives the class-pass capacity plan there.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageInitialCapacity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryStageResources (nodeBudget edgeBudget)
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
local notation "StageCapacity" => SourceCurrentAllocatedFiniteOrdinaryStageCapacity.StageCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial profiles and total budgets derive the universal earlier-prefix stage capacity plan. -/
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
    StageCapacity bits budget records values before fourth memo := by
  have domain := ChildrenShape.domain values profile
  have scanRanges := SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget
    SourceMemoGate.unconstrained (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
      (records.map SourceEqualityClassOrder.Record.paths) before fourth ready.good.native.machine.1.coherent available domain
  refine ⟨?_⟩
  intro selected middle savedFourth scan kept retained suppliedFuel suppliedReadFuel supplied suppliedHeap suppliedDone
  obtain ⟨_outcome, rfl, rfl, rfl⟩ := SourceCurrentAllocatedFiniteOrdinaryScan.scan scan ready available domain
  have sameLength : kept.length = records.length := by
    have lengths := congrArg List.length retained.fields.2
    simpa only [List.length_map] using lengths
  have sameKept := retained.fields.1.eq_of_length sameLength
  subst kept
  obtain ⟨chosen, heap, _requests, stable, _keeps, _semantic, _resident, chosenProfile,
    chosenHeight, chosenLength, _trace, _nodeCount, _edgeCount, chosenNodeSupply, chosenEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryCallerResources.required
      (SourceEqualitySelectedRequired.paths (records.map SourceEqualityClassOrder.Record.paths)) values
        before.native.machine.heap ready.semantic available profile
  obtain ⟨fuel, readFuel, enough⟩ := stable
  have chosenDone := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨rfl, rfl⟩ := SourceCurrentConjunctionRequiredActual.required_unique chosenDone suppliedDone
  have pathsProper : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, ∀ path ∈ paths, path ≠ [] := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact proper record present
  have pathsActive : ∀ paths ∈ records.map SourceEqualityClassOrder.Record.paths, Nontrivial paths := by
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (fields record present).2.2
  obtain ⟨requiredInventory, requiredReceipt⟩ := SourceCurrentConjunctionRequiredActual.verified
    formulas solver inventory scan ready admitted available pathsProper pathsActive correct scanRanges chosenDone
  obtain ⟨requiredMemos, _requiredReads, requiredValid, _unfolding, _queries⟩ := SourceCurrentRequiredQueryMemos.requireAll_memos
    fuel readFuel (SourceEqualitySelectedRequired.paths (records.map SourceEqualityClassOrder.Record.paths)) values chosen
      before.native.machine.heap heap chosenDone ready.semantic ready.costs available memos valid
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
  exact SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.complete formulas solver requiredInventory bits records
    (fun record member => (fields record member).1) (fun record member => (fields record member).2.2)
    chosen (advanceHeap before heap) memo requiredReceipt.ready requiredReceipt.admitted requiredReceipt.resident
    (physical.grows requiredReceipt.effects.keeps) profiles currentNative currentOutput covered requiredMemos requiredValid
    rows arity count depth bound chosenProfile (by omega) pathsBound
    (Nat.le_trans chosenHeight heightBound) passNodes passEdges

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageInitialCapacity
