import MicroCFTA.SourceCurrentConstrainedCapForceNumeric
set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.ForceNumericIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedSharedTargetState (State Ready store)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedSharedTargetForce (Receipt Retains)
open SourceEqualityClassTarget (operandPaths)
namespace Forecast
export SourceCurrentConstrainedCapSharedForecast (forceProfile forceFuel ForceReserved)
end Forecast
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "targetDepth" => SourceCurrentConstrainedCapMixedTarget.targetDepth
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An initial reserved Force produces the exact slot reused by a zero-fuel full-state warm call. -/
theorem produced_zero_warm (depth : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : Heap) (before : SourceCurrentAllocatedSharedTargetState.State (bits + 2)) (profile : Profile)
    (ready : Ready formulas solver inventory record values base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (known : Values base values)
    (domains : ∀ own ∈ record.paths, Domain (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (stored : Stored record values before) (bounded : ∀ original ∈ values, Cap depth original)
    (reserved : Forecast.ForceReserved bits values.length (operandPaths record.paths path)
      (before.targets path).isSome profile) :
    ∃ value after next final,
      Receipt formulas solver next record values base path before value after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.forceProfile values.length (operandPaths record.paths path)
        (before.targets path).isSome profile) after.checked ∧
      Stored record values after ∧ Cap (targetDepth depth (operandPaths record.paths path)) value ∧
      SourceCurrentAllocatedSharedTargetWorker.force
        (Forecast.forceFuel values.length (operandPaths record.paths path) (before.targets path).isSome profile)
        (Forecast.forceFuel values.length (operandPaths record.paths path) (before.targets path).isSome profile)
        (Forecast.forceFuel values.length (operandPaths record.paths path) (before.targets path).isSome profile)
        (Forecast.forceFuel values.length (operandPaths record.paths path) (before.targets path).isSome profile)
        (Forecast.forceFuel values.length (operandPaths record.paths path) (before.targets path).isSome profile)
        record values path before = .done value after ∧
      SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record values path after = .done value after := by
  obtain ⟨value, after, next, final, receipt, returned, numeric, saved, cap, done⟩ :=
    SourceCurrentConstrainedCapForceNumeric.complete depth formulas solver inventory record values base before profile
      ready frame fits known domains coherent active path member memos valid stored bounded reserved
  exact ⟨value, after, next, final, receipt, returned, numeric, saved, cap, done,
    SourceCurrentAllocatedSharedTargetWorker.force_hit 0 0 0 0 0 record values path after value receipt.present⟩
end MicroCFTA.ForceNumericIntegration
#print axioms MicroCFTA.ForceNumericIntegration.produced_zero_warm
#check @MicroCFTA.ForceNumericIntegration.produced_zero_warm
