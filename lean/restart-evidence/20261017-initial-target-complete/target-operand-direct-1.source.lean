import MicroCFTA.SourceCurrentConstrainedCapTargetForecast
import MicroCFTA.SourceCurrentAllocatedMergeNumericReplay
import MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion

/-!
# Initial profile bounds for the full allocated Target operand

The selected projection runs before Merge at its exact returned checked
state. The initial profile bounds both local schedules. The allocated
Merge replay retains equality operations and the completed first winner.
One shared fuel covers the four actual Operand worker parameters.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapTargetOperand
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
namespace Forecast
export SourceCurrentConstrainedCapTargetForecast (scalar operand operandFuel)
end Forecast
namespace Worker
export SourceCurrentAllocatedTargetWorker (operand projection merge Outcome)
end Worker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
variable {width : Nat}

private theorem scalar_fits {profile : Profile} {before : Checked width} (fits : Fits profile before) :
    SourceCurrentMemoMergeResourceControl.Fits (Forecast.scalar profile) before.native.machine.heap :=
  ⟨fits.stored.mono (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile),
    Nat.le_trans fits.nodes (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile),
    Nat.le_trans fits.edges (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile), Nat.zero_le _⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial selected support and a numeric profile construct the full allocated Operand return. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (profile : Profile) (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (domain : Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ result after saved final,
      SourceCurrentAllocatedTargetGraph.Operand path values before memo result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final ∧
      Frame formulas solver inventory after ∧ Fits (Forecast.operand path values.length profile) after ∧
      Worker.operand (Forecast.operandFuel path values.length profile) (Forecast.operandFuel path values.length profile)
        (Forecast.operandFuel path values.length profile) (Forecast.operandFuel path values.length profile)
        path values before memo = .done result after saved := by
  obtain ⟨result, after, saved, final, actual, receipt, returned, heapFits, _mass,
    projected, middle, current, projection, merged, _projectedFits, projectedDone, mergedDone, _projectStable, _mergeStable⟩ :=
    SourceCurrentConstrainedCapOperandNumeric.complete formulas solver inventory path values before memo
      (Forecast.scalar profile) frame available domain physicalStored covered memos valid (scalar_fits fits)
  have projectionWorker : Worker.projection (SourceCurrentProjectionNumeric.workFuel path)
      (SourceCurrentProjectionNumeric.readFuel path values.length (Forecast.scalar profile))
      path values before memo = .done projected middle memo := by
    simp only [Worker.projection, projectedDone]
    rw [← projection.advanced]
  have mergeWorker : Worker.merge
      (SourceCurrentConstrainedCapOperandNumeric.workFuel path values.length (Forecast.scalar profile))
      (SourceCurrentConstrainedCapOperandNumeric.selectionFuel path values.length (Forecast.scalar profile))
      projected middle memo = .done result after saved := by
    cases merged.actual with
    | done call =>
        have replay := SourceCurrentAllocatedMergeNumericReplay.call_replay call _ _ mergedDone
        simp only [Worker.merge, replay]
  have localDone : Worker.operand (SourceCurrentProjectionNumeric.workFuel path)
      (SourceCurrentProjectionNumeric.readFuel path values.length (Forecast.scalar profile))
      (SourceCurrentConstrainedCapOperandNumeric.workFuel path values.length (Forecast.scalar profile))
      (SourceCurrentConstrainedCapOperandNumeric.selectionFuel path values.length (Forecast.scalar profile))
      path values before memo = .done result after saved := by
    simpa only [Worker.operand, projectionWorker, Worker.Outcome.bind] using mergeWorker
  have numeric : Fits (Forecast.operand path values.length profile) after := by
    refine ⟨heapFits.nodes, heapFits.edges, ?_, heapFits.stored⟩
    simpa only [receipt.domains, SourceCurrentConstrainedCapTargetForecast.operand_domains] using fits.domains
  exact ⟨result, after, saved, final, actual, receipt, returned, numeric,
    SourceCurrentAllocatedTargetWorkerCompletion.operand_done_stable localDone
      (SourceCurrentConstrainedCapTargetForecast.operandFuel_projection path values.length profile)
      (SourceCurrentConstrainedCapTargetForecast.operandFuel_read path values.length profile)
      (SourceCurrentConstrainedCapTargetForecast.operandFuel_merge path values.length profile)
      (SourceCurrentConstrainedCapTargetForecast.operandFuel_selection path values.length profile)⟩

/-- The same constructed Operand also derives its output cap and retained semantic Merge laws. -/
theorem mixed_complete (depth : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (profile : Profile) (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (domain : Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (merged : MergeStored memo) (bounded : ∀ value ∈ values, Cap depth value) :
    ∃ result after saved final,
      SourceCurrentAllocatedTargetGraph.Operand path values before memo result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final ∧
      Frame formulas solver inventory after ∧ Fits (Forecast.operand path values.length profile) after ∧
      Worker.operand (Forecast.operandFuel path values.length profile) (Forecast.operandFuel path values.length profile)
        (Forecast.operandFuel path values.length profile) (Forecast.operandFuel path values.length profile)
        path values before memo = .done result after saved ∧
      MergeStored saved ∧ Cap (SourceCurrentConstrainedCapMixedTarget.operandDepth depth path) result := by
  obtain ⟨result, after, saved, final, actual, receipt, returned, numeric, done⟩ :=
    complete formulas solver inventory path values before memo profile frame fits available domain physicalStored covered memos valid
  have capped := SourceCurrentConstrainedCapMixedTarget.operand_receipt depth receipt frame.ready available domain
    physicalStored merged (SourceCurrentConstrainedCapOperandFrame.current frame) bounded
  exact ⟨result, after, saved, final, actual, receipt, returned, numeric, done, capped.1, capped.2.2⟩

end MicroCFTA.SourceCurrentConstrainedCapTargetOperand
