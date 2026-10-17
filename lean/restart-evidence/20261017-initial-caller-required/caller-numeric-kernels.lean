import MicroCFTA.SourceCurrentConstrainedCapClassCallerNumeric

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.CallerNumericWarmKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceEqualityProjectionPathDomain (ForestClosed)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local notation "foldProfile" => SourceCurrentConstrainedCapClassForecast.foldProfile
local notation "foldFuel" => SourceCurrentConstrainedCapClassForecast.foldFuel
local notation "Reserved" => SourceCurrentConstrainedCapClassForecast.Reserved
local notation "advance" => SourceCurrentAllocatedPartialState.advance
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Own initial pass completion retains both existing warm cells and their current physical language laws. -/
theorem retained_warm_cells (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Caller (bits + 2)) (memos : Memos) (profile : Profile)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (merged : MergeStored before.merge) (caps : ∀ value ∈ values, Cap depth value)
    (reserved : Reserved bits records values.length profile)
    (nodeCandidate nodeOriginal : SourceCurrentAllocatedPartialState.NodeRequest)
    (nodeHandle : Nat) (nodeResult : Value Symbol Guard)
    (nodePublished : before.nodeResults.table nodeCandidate.key = some nodeHandle)
    (nodeReturned : before.nodeResults.cells nodeHandle = some ⟨nodeOriginal, .returned nodeResult⟩)
    (edgeCandidate edgeOriginal : SourceCurrentAllocatedPartialState.EdgeRequest)
    (edgeHandle : Nat) (edgeResult : EdgeValue Symbol Guard)
    (edgePublished : before.edgeResults.table edgeCandidate.key = some edgeHandle)
    (edgeReturned : before.edgeResults.cells edgeHandle = some ⟨edgeOriginal, .returned edgeResult⟩) :
    ∃ results after saved next final,
      Post formulas solver next before (advance before after before.fourth saved) final ∧
      Frame formulas solver next after ∧ Fits (foldProfile records values.length profile) after ∧
      SourceCurrentAllocatedClassWorker.pass
        (foldFuel records values.length profile) (foldFuel records values.length profile)
        (foldFuel records values.length profile) (foldFuel records values.length profile)
        (foldFuel records values.length profile) (foldFuel records values.length profile)
        records values before.checked before.merge = .done results after saved ∧
      SourceCurrentAllocatedPartialState.beginNode nodeCandidate (advance before after before.fourth saved) =
        (nodeHandle, .ready nodeResult, advance before after before.fourth saved) ∧
      SourceCurrentAllocatedPartialState.beginEdge edgeCandidate (advance before after before.fourth saved) =
        (edgeHandle, .ready edgeResult, advance before after before.fourth saved) ∧
      Available after.native.machine.heap nodeResult ∧
      SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver nodeOriginal nodeResult ∧
      InternedEdgeResidency.EdgeResident after.native.machine.heap edgeResult ∧
      SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver edgeOriginal edgeResult := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, post, returned, numeric,
      _savedMerge, _outputCaps, _length, nodes, edges, _fourth, done, _larger⟩ :=
    SourceCurrentConstrainedCapClassCallerNumeric.complete depth formulas solver inventory records coherent active
      values before memos profile initial frame fits available domains merged caps reserved
  have nodeCell : (advance before after before.fourth saved).nodeResults.cells nodeHandle =
      some ⟨nodeOriginal, .returned nodeResult⟩ := by rw [nodes]; exact nodeReturned
  have edgeCell : (advance before after before.fourth saved).edgeResults.cells edgeHandle =
      some ⟨edgeOriginal, .returned edgeResult⟩ := by rw [edges]; exact edgeReturned
  have nodeGood := (post.context.sound.nodes nodeHandle _ nodeCell).returned nodeResult rfl
  have edgeGood := (post.context.sound.edges edgeHandle _ edgeCell).returned edgeResult rfl
  refine ⟨results, after, saved, next, final, post, returned, numeric, done, ?_, ?_,
    nodeGood.1, nodeGood.2, edgeGood.1, edgeGood.2⟩
  · exact SourceCurrentAllocatedPartialState.beginNode_ready nodeCandidate nodeOriginal _ nodeHandle nodeResult
      (by rw [nodes]; exact nodePublished) nodeCell
  · exact SourceCurrentAllocatedPartialState.beginEdge_ready edgeCandidate edgeOriginal _ edgeHandle edgeResult
      (by rw [edges]; exact edgePublished) edgeCell

#print axioms retained_warm_cells
#check @retained_warm_cells
end MicroCFTA.CallerNumericWarmKernels
