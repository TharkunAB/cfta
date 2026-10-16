import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClass
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion

/-!
# Constructed class edits from original forest resources

A class captures its actual entry forest and clears only local slots.
Original uniform limits bound every literal edit cost before execution.
The actual compiled edit derives its graph, receipts, and final supplies.
No reached range plan or completed edit is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassResources
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassEdits (Class ClassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
namespace Numbers
export SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers (leafNodes leafEdges outputRows outputArity)
end Numbers
namespace Counts
export SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds (nodeCount edgeCount)
end Counts
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity

/-- Every original position permits a complete target and query, plus node reconstruction. -/
def nodeBudget (record : Record) (rows arity count depth bound : Nat) : Nat :=
  count * (1 + arity * Counts.edgeCount rows arity bound) * Numbers.leafNodes record rows arity count depth bound rows arity bound +
    count * Counts.nodeCount rows arity bound

/-- The original position bound also pays for all literal edge reconstruction. -/
def edgeBudget (record : Record) (rows arity count depth bound : Nat) : Nat :=
  count * (1 + arity * Counts.edgeCount rows arity bound) * Numbers.leafEdges record rows arity count depth bound rows arity bound +
    count * Counts.edgeCount rows arity bound

/-- Captured and current forests share the same original row limit at class entry. -/
def outputRows (record : Record) (rows count depth bound : Nat) : Nat :=
  Numbers.outputRows record rows count depth bound rows

/-- The fixed result arity includes the original arity and native sentinels. -/
def outputArity (arity : Nat) : Nat := Numbers.outputArity arity arity

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial forest limits and cumulative headroom construct the complete current class. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (record : Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget record rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget record rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after saved next final requests,
      ∃ actual : Class record values before memo results after saved,
        ClassReads formulas solver actual memos final ∧
        Receipt formulas solver next record values before memo results after saved memos final ∧
        SourceCurrentAllocatedClassWorkerCompletion.StableRun
          (fun e p h m s n => SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo) results after saved ∧
        NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
        ChildrenShape (outputRows record rows count depth bound) (outputArity arity) results ∧
        All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound ∧
        Trace before.native.machine.heap after.native.machine.heap requests ∧
        nodeRequests requests ≤ nodeBudget record rows arity count depth bound ∧
        edgeRequests requests ≤ edgeBudget record rows arity count depth bound ∧ Capacity bits after ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget record rows arity count depth bound ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget record rows arity count depth bound := by
  have domain := ChildrenShape.domain values profile
  have domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values :=
    fun path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain _
  have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
    before.native.machine.heap before memo ready admitted (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) physical covered
  have initialStored := SourceCurrentAllocatedFiniteOrdinarySharedProfiles.initial_stored
    (rows := SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rows count depth bound)
    (arity := max arity 1) (bound := bound) before memo native output profiles
  have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
    obtain ⟨entries, built⟩ := compiled_children record coherent active
    rw [built]
    exact compiled_safe record coherent values domains entries built
  have costs := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.forest_profile
    (Numbers.leafNodes record rows arity count depth bound rows arity bound)
    (Numbers.leafEdges record rows arity count depth bound rows arity bound)
    values profile count bound lengthBound heightBound
  obtain ⟨results, shared, _editInventory, final, requests, lower, lowerReads, _editReceipt,
    sharedStored, resultProfile, narrowed, sameLength, _stable, trace, nodeCount, edgeCount,
    capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryEditResources.list formulas solver bits record values before.native.machine.heap
      rows arity count depth bound rows arity bound available coherent active profile lengthBound pathsBound heightBound
      inventory (compiled record) values (SourceCurrentAllocatedSharedTargetState.initial before memo)
      initialReady initialStored available profile heightBound (compiled_populated record) (compiled_allowed record)
      safe memos valid (by change before.native.machine.heap.nodes.next + _ ≤ 2 ^ bits; unfold nodeBudget at nodes; omega)
      (by change before.native.machine.heap.edges.next + _ ≤ 2 ^ (bits + 2); unfold edgeBudget at edges; omega)
  have actual : Class record values before memo results shared.checked shared.memo := .edit lower
  have reads : ClassReads formulas solver actual memos final := .edit lowerReads
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassEdits.verified formulas solver inventory record coherent active reads
    ready admitted available domains physical covered valid
  refine ⟨results, shared.checked, shared.memo, next, final, requests, actual, reads, receipt,
    SourceCurrentAllocatedClassWorkerCompletion.class_complete actual, sharedStored.native, sharedStored.output,
    sharedStored.merge, resultProfile, narrowed, sameLength,
    Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_height narrowed) heightBound,
    trace, ?_, ?_, capacity, ?_, ?_⟩
  · exact Nat.le_trans nodeCount costs.1
  · exact Nat.le_trans edgeCount costs.2
  · unfold nodeBudget
    exact Nat.le_trans nodeSupply (Nat.add_le_add_left costs.1 _)
  · unfold edgeBudget
    exact Nat.le_trans edgeSupply (Nat.add_le_add_left costs.2 _)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassResources
