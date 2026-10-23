import MicroCFTA.SourceCurrentOriginalRowGroupChain
import MicroCFTA.SourceCurrentOriginalRowClusterAdmission

namespace MicroCFTA.SourceCurrentOriginalRowGroupAdmission
open Cache Language IntersectSchedule InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionInputView InternedProbeProvenance
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "NativeIdle" => SourceRecursiveIntersectionNative.Idle
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)
variable (inventory : Inventory)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
local notation "holds" => guardHolds formulas solver
local notation "inputs" => inventory.inputs holds
local notation "inputView" => view inventory.source holds
local notation "inputModel" => finiteInputMeaning inputView inputs
local notation "inputRanked" => finiteRankedInput inputView inputs
local notation "Stable" => SourceCurrentSameSymbolEdgeStable.Stable inputView inputModel inputRanked holds
local notation "Current" => At formulas solver inventory
local notation "PairInputs" => (fun pair : Edge × Edge =>
  SourceCurrentAllocatedNativeContextCache.EdgeInputs inputView inputModel
    (SourceRecursiveIntersectionThunks.EdgeRequest.mk IntersectionEmptyDomain.emptyDomain (Prod.fst pair) (Prod.snd pair)))

/-- Retain admission at every boundary of the same supplied original-row group chain. -/
theorem groups_admitted
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (parent : Value Symbol Guard) (member : parent ∈ inventory.roots)
    (entries : List (Symbol × List Edge))
    (iteration : SourceCurrentMergeGrouping.Iteration
      (SourceCurrentPrependGrouping.fromRows (fun edge : Edge => edge.entry.key.symbol)
        (nodeEdges parent)) entries)
    (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (initialValid : Cache.Valid initialDomains)
    (before : Wrapper (bits + 2))
    (current : Current before.checked)
    (admitted : ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
      before.memo.cells handle = some ⟨pair, .returned value⟩ →
      PairInputs (if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair))
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨inventory.source.nodes.next, inventory.source.edges.next,
        initialDomains.next + (SourceRecursiveIntersectionSourceInventory.domains inventory.source).length, 0⟩)
    (fuels : Fin entries.length → Nat) (kept : Fin entries.length → List Edge)
    (states : Fin (entries.length + 1) → Wrapper (bits + 2))
    (start : states 0 = before)
    (steps : ∀ index : Fin entries.length,
      SourceCurrentOriginalRowClusterScan.execute (fuels index)
        (.cluster (entries.get index).2.reverse []) (states index.castSucc) =
        .done (kept index) (states index.succ))
    (packets : ∀ index : Fin entries.length,
      Stable (states index.castSucc) ∧
      Good (states index.castSucc).checked ∧
      SemanticReady (states index.castSucc).checked.native.machine.heap ∧
      SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionSourceInventory.domains inventory.source)
        initialDomains (states index.castSucc).checked.native.machine.domains ∧
      NativeIdle (states index.castSucc).checked.native) :
    ∀ index : Fin (entries.length + 1),
      Current (states index).checked ∧
      ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
        (states index).memo.cells handle = some ⟨pair, .returned value⟩ →
        PairInputs (if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair) := by
  have reversed : SourceCurrentMergeGrouping.Iteration
      (SourceCurrentPrependGrouping.reverseTable
        (SourceCurrentPrependGrouping.fromRows (fun edge : Edge => edge.entry.key.symbol)
          (nodeEdges parent)))
      (entries.map (fun entry => (entry.1, entry.2.reverse))) := by
    exact SourceCurrentPrependGrouping.iteration_reverse _ entries iteration
  refine Fin.induction ?_ ?_
  · rw [start]
    exact ⟨current, admitted⟩
  · intro index ih
    obtain ⟨sourceStable, sourceGood, sourceSemantic, sourceTrace, sourceIdle⟩ := packets index
    obtain ⟨sourceCurrent, sourceAdmitted⟩ := ih
    have included : ((entries.get index).1, (entries.get index).2.reverse) ∈
        entries.map (fun entry => (entry.1, entry.2.reverse)) := by
      exact List.mem_map.mpr ⟨entries.get index, List.get_mem entries index, rfl⟩
    have found : SourceCurrentPrependGrouping.reverseTable
        (SourceCurrentPrependGrouping.fromRows (fun edge : Edge => edge.entry.key.symbol)
          (nodeEdges parent)) (entries.get index).1 = some ((entries.get index).2.reverse) := by
      exact (reversed.lookup (entries.get index).1 (entries.get index).2.reverse).mp included
    have contents : (entries.get index).2.reverse = (nodeEdges parent).filter
        (fun edge => decide (edge.entry.key.symbol = (entries.get index).1)) := by
      rw [SourceCurrentPrependGrouping.reverse_fromRows] at found
      exact ((SourceCurrentMergeGrouping.lookup_some
        (fun edge : Edge => edge.entry.key.symbol) (nodeEdges parent)
        (entries.get index).1 (entries.get index).2.reverse).mp found).2
    exact SourceCurrentOriginalRowClusterAdmission.completed_admitted inventory formulas solver
      bits parent member (entries.get index).1 initialDomains initialValid
      (states index.castSucc) sourceStable sourceGood sourceCurrent
      sourceSemantic sourceTrace sourceIdle sourceAdmitted room
      (fuels index) (kept index) (states index.succ)
      (by rw [← contents]; exact steps index)

end MicroCFTA.SourceCurrentOriginalRowGroupAdmission
