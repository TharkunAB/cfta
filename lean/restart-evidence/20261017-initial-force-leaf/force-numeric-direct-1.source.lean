import MicroCFTA.SourceCurrentConstrainedCapSharedForecast
import MicroCFTA.SourceCurrentConstrainedCapTargetNumeric
import MicroCFTA.SourceCurrentConstrainedCapMixedShared
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorker

/-!
# Initial numeric reservations for shared target forcing

A hit retains the complete state and needs no query reservation. A miss
constructs its actual Target from the initial numeric profile. Its full
historical receipt is installed before the existing slot certificate is
used. The captured forest, class paths, and current inventory stay distinct.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapForceNumeric
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

private theorem miss_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : Heap} {path : EqualityNormalize.Path} {before : State (bits + 2)}
    {value : Value Symbol Guard} {checked : Checked (bits + 2)} {saved : Memo} {memos final : Memos}
    (ready : Ready formulas solver inventory record values base before) (member : path ∈ record.paths)
    (absent : before.targets path = none)
    (actual : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path)
      before.checked before.memo value checked saved)
    (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final)
    (receipt : SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values (operandPaths record.paths path)
      before.checked before.memo value checked saved memos final)
    (included : SourceCurrentAllocatedClassTarget.SelectedIncludes formulas solver record values path value) :
    Receipt formulas solver next record values base path before value (store before path value checked saved) memos final := by
  refine ⟨.miss absent actual, .miss absent reads, ready.store path member actual reads receipt,
    receipt.effects, receipt.extension, receipt.available, receipt.closed, ?_, ?_, receipt.retained,
    receipt.globals, included⟩
  · simp only [store, put, ite_true]
  · intro other target present
    by_cases same : other = path
    · subst other
      rw [absent] at present
      cases present
    · simpa only [store, put, same, ite_false] using present

/-- Initial class facts and numeric reservations construct the complete full-state Force return. -/
theorem complete (depth : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : Heap) (before : State (bits + 2)) (profile : Profile)
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
        record values path before = .done value after := by
  have operandDomains := SourceCurrentTargetPathComplete.operand_domains record values domains path
  cases present : before.targets path with
  | some value =>
      have slot := ready.receipts path value present
      have available := slot.available
      have physicalReady : SourceCurrentConjunctionRowsAllocation.Ready (physical before.checked) :=
        ⟨ready.checked.semantic, ready.checked.costs, ready.checked.good.operations, ready.checked.good.fields⟩
      have effects := SourceCurrentConjunctionRowsAllocation.Effects.refl _ physicalReady
      have receipt : Receipt formulas solver inventory record values base path before value before memos memos :=
        ⟨.hit present, .hit present memos, ready, effects, .refl _, available.1, available.2,
          present, Retains.refl _, extends_refl _,
          ⟨effects.keeps, ready.checked.semantic, ready.checked.costs, valid, extends_refl _, rfl⟩,
          slot.included coherent active⟩
      have capped := SourceCurrentConstrainedCapMixedShared.force_receipt receipt ready known stored depth bounded operandDomains
      refine ⟨value, before, inventory, memos, receipt, frame, ?_, capped.1, capped.2, ?_⟩
      · simpa only [present, Option.isSome, Forecast.forceProfile] using fits
      · simp only [SourceCurrentAllocatedSharedTargetWorker.force, present]
  | none =>
      have available : Values before.checked.native.machine.heap values :=
        fun value member => ready.captured.available value (known value member)
      have targetReserved : SourceCurrentConstrainedCapTargetForecast.TargetReserved bits values.length
          (operandPaths record.paths path) profile := by
        simpa only [present, Option.isSome, Forecast.ForceReserved] using reserved
      obtain ⟨next, value, checked, saved, final, actual, reads, receipt, returned, finalFits, _merged, _cap, done⟩ :=
        SourceCurrentConstrainedCapTargetNumeric.complete depth formulas solver inventory values
          (operandPaths record.paths path) before.checked before.memo profile frame fits available operandDomains
          ready.stored ready.covered memos valid stored.merge bounded targetReserved
      have included := SourceCurrentAllocatedClassTarget.receipt_included receipt coherent active member
      have forced := miss_receipt ready member present actual reads receipt included
      have capped := SourceCurrentConstrainedCapMixedShared.force_receipt forced ready known stored depth bounded operandDomains
      have worker : SourceCurrentAllocatedSharedTargetWorker.force
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          record values path before = .done value (store before path value checked saved) := by
        simp only [SourceCurrentAllocatedSharedTargetWorker.force, present, done]
      refine ⟨value, store before path value checked saved, next, final, forced, returned, ?_, capped.1, capped.2, ?_⟩
      · simpa only [present, Option.isSome, Forecast.forceProfile, store] using finalFits
      · simpa only [present, Option.isSome, Forecast.forceFuel] using worker

end MicroCFTA.SourceCurrentConstrainedCapForceNumeric
