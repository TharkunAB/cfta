import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResources

namespace MicroCFTA.TargetResourcesIndependentIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "N" => SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget
local notation "E" => SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget
local notation "StableRun" => SourceCurrentAllocatedTargetWorkerCompletion.StableRun
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- The second target uses the first complete returned state and inventory.
theorem two_three_path_targets (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (values : List (Value Symbol Guard)) (seed first second : List Int)
    (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (profiles : Profiles memo) (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ path ∈ [seed, first, second], path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + 2 * N rows arity count depth bound 3 ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + 2 * E rows arity count depth bound 3 ≤ 2 ^ (bits + 2)) :
    ∃ result middle saved next final later after last lastInventory lastGlobals firstRequests lastRequests,
      ∃ actual : Target values [seed, first, second] before memo result middle saved,
      ∃ laterActual : Target values [seed, first, second] middle saved later after last,
        StableRun (fun p h m s n => SourceCurrentAllocatedTargetWorker.target p h m s n
          values [seed, first, second] before memo) result middle saved ∧
        StableRun (fun p h m s n => SourceCurrentAllocatedTargetWorker.target p h m s n
          values [seed, first, second] middle saved) later after last ∧
        TargetReads formulas solver actual memos final ∧
        Receipt formulas solver next values [seed, first, second] before memo result middle saved memos final ∧
        TargetReads formulas solver laterActual final lastGlobals ∧
        Receipt formulas solver lastInventory values [seed, first, second] middle saved later after last final lastGlobals ∧
        Profiles last ∧ NativeStored after.native ∧ OutputStored after.native ∧
        Trace before.native.machine.heap after.native.machine.heap (firstRequests ++ lastRequests) ∧
        nodeRequests (firstRequests ++ lastRequests) ≤ 2 * N rows arity count depth bound 3 ∧
        edgeRequests (firstRequests ++ lastRequests) ≤ 2 * E rows arity count depth bound 3 ∧
        Capacity bits after ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + 2 * N rows arity count depth bound 3 ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 2 * E rows arity count depth bound 3 := by
  obtain ⟨result, middle, saved, next, final, firstRequests, actual, stable, reads, receipt,
    firstProfiles, firstNative, firstOutput, _resultProfile, _resultHeight, firstTrace,
    firstNodes, firstEdges, _middleCapacity, firstNodeSupply, firstEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTargetResources.target_complete formulas solver inventory bits
      values [seed, first, second] before memo ready admitted available physical profiles native output
      covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound (by simpa using (show
        before.native.machine.heap.nodes.next + N rows arity count depth bound 3 ≤ 2 ^ bits by omega))
      (by simpa using (show before.native.machine.heap.edges.next + E rows arity count depth bound 3 ≤ 2 ^ (bits + 2) by omega))
  change middle.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + N rows arity count depth bound 3 at firstNodeSupply
  change middle.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + E rows arity count depth bound 3 at firstEdgeSupply
  obtain ⟨later, after, last, lastInventory, lastGlobals, lastRequests, laterActual, laterStable,
    laterReads, laterReceipt, lastProfiles, lastNative, lastOutput, _laterProfile, _laterHeight,
    lastTrace, lastNodes, lastEdges, finalCapacity, lastNodeSupply, lastEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTargetResources.target_complete formulas solver next bits
      values [seed, first, second] middle saved receipt.ready receipt.admitted receipt.originals
      receipt.stored firstProfiles firstNative firstOutput receipt.covered final receipt.globals.valid
      rows arity count depth bound profile lengthBound pathsBound heightBound
      (by simpa using (show middle.native.machine.heap.nodes.next + N rows arity count depth bound 3 ≤ 2 ^ bits by
        omega))
      (by simpa using (show middle.native.machine.heap.edges.next + E rows arity count depth bound 3 ≤ 2 ^ (bits + 2) by
        omega))
  have combined := firstTrace.trans lastTrace
  have totalNodes : nodeRequests (firstRequests ++ lastRequests) ≤ 2 * N rows arity count depth bound 3 := by
    rw [nodeRequests_append]
    change nodeRequests firstRequests ≤ N rows arity count depth bound 3 at firstNodes
    change nodeRequests lastRequests ≤ N rows arity count depth bound 3 at lastNodes
    omega
  have totalEdges : edgeRequests (firstRequests ++ lastRequests) ≤ 2 * E rows arity count depth bound 3 := by
    rw [edgeRequests_append]
    change edgeRequests firstRequests ≤ E rows arity count depth bound 3 at firstEdges
    change edgeRequests lastRequests ≤ E rows arity count depth bound 3 at lastEdges
    omega
  have supply := combined.next_le
  exact ⟨result, middle, saved, next, final, later, after, last, lastInventory, lastGlobals,
    firstRequests, lastRequests, actual, laterActual, stable, laterStable, reads, receipt,
    laterReads, laterReceipt, lastProfiles, lastNative, lastOutput, combined, totalNodes, totalEdges,
    finalCapacity, by omega, by omega⟩

#print axioms two_three_path_targets
#check @two_three_path_targets
end MicroCFTA.TargetResourcesIndependentIntegration
