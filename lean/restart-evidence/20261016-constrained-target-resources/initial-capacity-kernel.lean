import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetInitialCapacity

namespace MicroCFTA.TargetInitialCapacityIndependentIntegration
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

-- Initial budgets discharge the universal plan at every raw earlier head and tail.
theorem initial_budgets_to_universal_ranges (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (nodes : before.native.machine.heap.nodes.next + N rows arity count depth bound 3 ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + E rows arity count depth bound 3 ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.TargetCapacity bits values [seed, first, second] before memo ∧
    TargetRanges values [seed, first, second] before memo ∧
    ∀ head middle current tail later saved,
      Operand first values before memo head middle current →
      Fold values seed [second] middle current tail later saved →
      Capacity bits later ∧
      SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain head tail)) later := by
  have plan := SourceCurrentAllocatedFiniteOrdinaryTargetInitialCapacity.target_capacity
    formulas solver inventory bits values [seed, first, second] before memo ready admitted available
    physical profiles native output covered memos valid rows arity count depth bound profile
    lengthBound pathsBound heightBound nodes edges
  have ranges := SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.target_ranges
    formulas solver inventory bits values [seed, first, second] before memo ready admitted available
    (ChildrenShape.domain values profile) physical profiles.domain native covered plan memos valid
  refine ⟨plan, ranges, ?_⟩
  intro head middle current tail later saved operand rest
  have foldPlan : SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.FoldCapacity bits values seed [first, second] before memo := plan
  exact ⟨foldPlan.query operand rest, ranges.2 _ _ _ _ _ _ operand rest⟩

#print axioms initial_budgets_to_universal_ranges
#check @initial_budgets_to_universal_ranges
end MicroCFTA.TargetInitialCapacityIndependentIntegration
