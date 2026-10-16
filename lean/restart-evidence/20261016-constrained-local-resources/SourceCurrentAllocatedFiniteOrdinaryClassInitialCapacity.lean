import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassCapacity

/-!
# Existing class capacity from initial forest resources

The class captures its actual entry forest and clears only local slots.
Original profile bounds derive the total compiled edit cost.
Initial headroom derives each existing numeric capacity obligation.
No completed class or future returned-state fact is an initial premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassInitialCapacity
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

open SourceCurrentAllocatedFiniteOrdinaryClassResources (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryClassCapacity (ClassCapacity)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial profiles and total headroom derive the existing compiled class capacity plan. -/
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
    ClassCapacity bits record values before memo := by
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
  exact SourceCurrentAllocatedFiniteOrdinaryEditInitialCapacity.list formulas solver bits record values before.native.machine.heap
    rows arity count depth bound rows arity bound available coherent active profile lengthBound pathsBound heightBound
    inventory (compiled record) values (SourceCurrentAllocatedSharedTargetState.initial before memo)
    initialReady initialStored available profile heightBound (compiled_populated record) (compiled_allowed record)
    safe memos valid
    (by change before.native.machine.heap.nodes.next + _ ≤ 2 ^ bits; unfold nodeBudget at nodes; omega)
    (by change before.native.machine.heap.edges.next + _ ≤ 2 ^ (bits + 2); unfold edgeBudget at edges; omega)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassInitialCapacity
