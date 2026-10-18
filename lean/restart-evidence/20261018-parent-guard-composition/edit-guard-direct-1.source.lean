import MicroCFTA.SourceCurrentTargetGuardAlphabet
import MicroCFTA.SourceCurrentForceNumeric
import MicroCFTA.SourceCurrentLeafNumeric

/-!
# Initial guard carriers for shared Force and Leaf

A present slot writes no guard. A missing slot follows its initial Target
schedule. Leaf then permits the predicted native instructions after Force.
Both producers construct the same full shared return and guard carrier.
This module does not assert a complete Edit or forest carrier.
-/
namespace MicroCFTA.SourceCurrentEditGuardAlphabet
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedSharedTargetState (State Ready store advance)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedSharedTargetForce (Receipt Retains)
open SourceEqualityClassTarget (operandPaths)
namespace Forecast
export SourceCurrentConstrainedCapSharedForecast
  (forceProfile forceFuel ForceReserved leafProfile leafFuel LeafReserved)
end Forecast
namespace Worker
export SourceCurrentAllocatedSharedTargetWorker (leaf step Outcome)
end Worker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "advanceAlphabet" => SourceCurrentNativeGuardAlphabet.advance
local notation "operands" => SourceEqualityClassTarget.operandPaths
local notation "queryFuel" => SourceCurrentConstrainedCapTargetForecast.queryFuel
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound

/-- A warm slot has no guard extension. A miss follows its initial Target schedule. -/
def forceCount (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) : Nat :=
  if found then 0 else SourceCurrentTargetGuardAlphabet.targetCount count paths profile

/-- The initial Force profile bounds all instructions in the subsequent Leaf query. -/
def leafCount (count : Nat) (paths : List (List Int)) (found : Bool) (profile : Profile) : Nat :=
  let query := Forecast.forceProfile count paths found profile
  forceCount count paths found profile + instructionBound query.nodes query.edges query.mass

variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem miss_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : Heap} {path : EqualityNormalize.Path} {before : SourceCurrentAllocatedSharedTargetState.State (bits + 2)}
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
theorem force_complete (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (reserved : Forecast.ForceReserved bits values.length (operandPaths record.paths path)
      (before.targets path).isSome profile)
    (knownAlphabet : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ value after next final,
      Receipt formulas solver next record values base path before value after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.forceProfile values.length (operandPaths record.paths path)
        (before.targets path).isSome profile) after.checked ∧
      Carrier (fun guard => guard ∈ advanceAlphabet alphabet
        (forceCount values.length (operandPaths record.paths path) (before.targets path).isSome profile))
        after.checked.native.machine.heap ∧
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
      refine ⟨value, before, inventory, memos, receipt, frame, ?_, ?_, ?_⟩
      · simpa only [present, Option.isSome, SourceCurrentConstrainedCapSharedForecast.forceProfile_hit] using fits
      · simpa only [present, Option.isSome, forceCount, ite_true,
          SourceCurrentNativeGuardAlphabet.advance_zero] using knownAlphabet
      · simp only [SourceCurrentAllocatedSharedTargetWorker.force, present]
  | none =>
      have available : Values before.checked.native.machine.heap values :=
        fun value member => ready.captured.available value (known value member)
      have targetReserved : SourceCurrentConstrainedCapTargetForecast.TargetReserved bits values.length
          (operandPaths record.paths path) profile := by
        simpa only [present, Option.isSome, SourceCurrentConstrainedCapSharedForecast.forceReserved_miss] using reserved
      obtain ⟨next, value, checked, saved, final, actual, reads, receipt, returned, finalFits, targetKnown, done⟩ :=
        SourceCurrentTargetGuardAlphabet.complete alphabet formulas solver inventory values
          (operandPaths record.paths path) before.checked before.memo profile frame fits available operandDomains
          ready.stored ready.covered memos valid targetReserved knownAlphabet
      have included := SourceCurrentAllocatedClassTarget.receipt_included receipt coherent active member
      have forced := miss_receipt ready member present actual reads receipt included
      have worker : SourceCurrentAllocatedSharedTargetWorker.force
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          (SourceCurrentConstrainedCapTargetForecast.targetFuel values.length (operandPaths record.paths path) profile)
          record values path before = .done value (store before path value checked saved) := by
        simp only [SourceCurrentAllocatedSharedTargetWorker.force, present, done]
      refine ⟨value, store before path value checked saved, next, final, forced, returned, ?_, ?_, ?_⟩
      · simpa only [present, Option.isSome, SourceCurrentConstrainedCapSharedForecast.forceProfile_miss, store] using finalFits
      · simpa only [present, Option.isSome, forceCount, Bool.false_eq_true, ite_false, store] using targetKnown
      · simpa only [present, Option.isSome, SourceCurrentConstrainedCapSharedForecast.forceFuel_miss] using worker

variable {width : Nat}

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
theorem leaf_complete (alphabet : List Guard)
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
    (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (reserved : Forecast.LeafReserved bits values.length (operands record.paths path) (before.targets path).isSome profile)
    (knownAlphabet : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ result after next final,
      SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values base path input before result after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.leafProfile values.length (operands record.paths path) (before.targets path).isSome profile) after.checked ∧
      Carrier (fun guard => guard ∈ advanceAlphabet alphabet
        (leafCount values.length (operands record.paths path) (before.targets path).isSome profile))
        after.checked.native.machine.heap ∧
      Worker.leaf (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        (Forecast.leafFuel values.length (operands record.paths path) (before.targets path).isSome profile)
        record values path input before = .done result after := by
  obtain ⟨target, middle, forceInventory, current, first, forceFrame, forceFits, forceKnown, forceDone⟩ :=
    force_complete alphabet formulas solver inventory record values base before profile
      ready frame fits known domains coherent active path member memos valid reserved.1 knownAlphabet
  obtain ⟨next, fuel, result, checked, query, queryKnown⟩ := SourceCurrentGeneratedQueryGuardResources.complete
    (advanceAlphabet alphabet (forceCount values.length (operands record.paths path) (before.targets path).isSome profile))
    (Forecast.forceProfile values.length (operands record.paths path) (before.targets path).isSome profile)
    formulas solver forceInventory middle.checked forceFrame forceFits reserved.2
    target input first.available (first.effects.keeps.available input available) first.closed closed forceKnown
    current first.globals.valid
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
  refine ⟨result, advance middle checked, next, current, of_parts first query.query, query.frame, query.fits, ?_, ?_⟩
  · simpa only [leafCount, SourceCurrentGeneratedQueryGuardResources.forecast,
      SourceCurrentNativeGuardAlphabet.advance_add] using queryKnown
  · simp only [SourceCurrentAllocatedSharedTargetWorker.leaf, forced,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.bind, returned]

end MicroCFTA.SourceCurrentEditGuardAlphabet
