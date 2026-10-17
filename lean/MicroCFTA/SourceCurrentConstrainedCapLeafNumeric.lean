import MicroCFTA.SourceCurrentConstrainedCapForceNumeric
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerStability

/-!
# Complete shared Leaf execution from initial numeric reservations

Force uses its actual initial slot branch. Its literal returned target
precedes the checked query. Initial forecasts bound both stages and retain
the complete shared state, query Frame, inventories, memos, and cap laws.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapLeafNumeric
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedSharedTargetState (advance Ready)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConstrainedCap (Cap)
namespace Forecast
export SourceCurrentConstrainedCapSharedForecast (forceProfile leafProfile LeafReserved leafFuel)
end Forecast
namespace Worker
export SourceCurrentAllocatedSharedTargetWorker (leaf step Outcome)
end Worker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "operands" => SourceEqualityClassTarget.operandPaths
local notation "leafDepth" => SourceCurrentConstrainedCapMixedShared.leafDepth
local notation "queryFuel" => SourceCurrentConstrainedCapTargetForecast.queryFuel
variable {width bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem of_parts
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : Heap} {path : EqualityNormalize.Path} {input target result : Value Symbol Guard}
    {before middle : Shared width} {checked : SourceEqualityNativeDemand.State width} {memos current : Memos}
    (first : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver inventory record values base path
      before target middle memos current)
    (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result checked current) :
    SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values base path input
      before result (advance middle checked) memos current := by
  have queryGlobal : SourceCurrentSubsumesQueryMemos.Effect middle.checked.native.machine.heap checked.native.machine.heap current current :=
    ⟨query.effects.keeps, query.ready.semantic, query.ready.costs, query.globals, extends_refl _, rfl⟩
  refine ⟨.apply first.actual query.actual,
    .apply (forced := first.actual) (step := query.actual) first query,
    first.ready.advance next checked query.ready query.admitted query.effects,
    first.effects.trans query.effects, first.extension.trans query.extension,
    query.available, query.closed, first.slots, first.retained,
    SourceCurrentMemoMergeQueryMemos.effect_trans first.globals queryGlobal, ?_, ?_⟩
  · intro ambient term accepted
    exact ((query.meaning ambient term).mp accepted).2
  · intro ambient symbol terms part accepted satisfied selected present
    exact (query.meaning ambient part).mpr ⟨first.included ambient symbol terms part accepted satisfied selected, present⟩

/-- Initial class support and numeric room construct Force followed by the actual checked query. -/
theorem complete (capturedDepth inputDepth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : Heap) (before : Shared (bits + 2)) (profile : Profile)
    (ready : Ready formulas solver inventory record values base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (known : Values base values)
    (domains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (input : Value Symbol Guard)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (inputCap : Cap Plain inputDepth input) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (stored : Stored record values before) (bounded : ∀ original ∈ values, Cap Plain capturedDepth original)
    (reserved : Forecast.LeafReserved bits values.length (operands record.paths path) (before.targets path).isSome profile) :
    ∃ result after next final,
      SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values base path input before result after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.leafProfile values.length (operands record.paths path) (before.targets path).isSome profile) after.checked ∧
      Stored record values after ∧ Cap Plain (leafDepth record path capturedDepth inputDepth) result ∧
      Worker.leaf (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        record values path input before = .done result after := by
  obtain ⟨target, middle, forceInventory, current, first, forceFrame, forceFits, forceStored, forceCap, forceDone⟩ :=
    SourceCurrentConstrainedCapForceNumeric.complete capturedDepth formulas solver inventory record values base before profile
      ready frame fits known domains coherent active path member memos valid stored bounded reserved.1
  obtain ⟨next, fuel, result, checked, query⟩ := SourceCurrentConstrainedCapGeneratedQueryResources.complete
    (Forecast.forceProfile values.length (operands record.paths path) (before.targets path).isSome profile)
    (leafDepth record path capturedDepth inputDepth) formulas solver forceInventory middle.checked forceFrame forceFits reserved.2
    target input first.available (first.effects.keeps.available input available) first.closed closed
    (forceCap.mono (Nat.le_max_left _ _)) (inputCap.mono (Nat.le_max_right _ _)) current first.globals.valid
  have forceEnough := SourceCurrentConstrainedCapSharedForecast.leafFuel_force
    values.length (operands record.paths path) (before.targets path).isSome profile
  have queryEnough := SourceCurrentConstrainedCapSharedForecast.leafFuel_query
    values.length (operands record.paths path) (before.targets path).isSome profile
  have forced := SourceCurrentAllocatedSharedTargetWorkerStability.force_done_stable forceDone
    forceEnough forceEnough forceEnough forceEnough forceEnough
  have stepDone : Worker.step
      (queryFuel (Forecast.forceProfile values.length (operands record.paths path) (before.targets path).isSome profile))
      target input middle = .done result (advance middle checked) := by
    simp only [SourceCurrentAllocatedSharedTargetWorker.step, SourceCurrentConstrainedCapTargetForecast.queryFuel, query.done]
  have returned := SourceCurrentAllocatedSharedTargetWorkerStability.step_done_stable stepDone queryEnough
  refine ⟨result, advance middle checked, next, current, of_parts first query.query, query.frame, query.fits,
    SourceCurrentConstrainedCapMixedShared.advance_stored record values middle checked forceStored
      (SourceCurrentConstrainedCapOperandFrame.current query.frame), query.joint.cap, ?_⟩
  simp only [SourceCurrentAllocatedSharedTargetWorker.leaf, forced,
    SourceCurrentAllocatedSharedTargetWorker.Outcome.bind, returned]

end MicroCFTA.SourceCurrentConstrainedCapLeafNumeric
