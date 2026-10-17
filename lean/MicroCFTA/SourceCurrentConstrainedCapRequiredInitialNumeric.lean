import MicroCFTA.SourceCurrentConstrainedCapRequiredNumeric
import MicroCFTA.SourceCurrentConstrainedCapSelectedRequiredComplete

/-!
# Complete selected Required from initial numeric resources

Original primary certificates construct the actual Required graph.
The same return fits the forecast from the initial trie and forest count.
Both worker and reader bounds are fixed from those original inputs.
The full query Frame, caller Post, caps, and exact tables remain tied to it.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRequiredInitialNumeric
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "advance" => SourceCurrentAllocatedPartialState.advance
variable {width : Nat}

/-- The initial trie and literal forest count fix the complete Required profile. -/
noncomputable def forecast (paths : List (List Int)) (count : Nat) (profile : Profile) : Profile :=
  SourceCurrentConstrainedCapRequiredForecast.scan
    (SourceCurrentConstrainedCapRequiredForecast.planProfile (sizeOf (SourceEqualityNeeded.build paths))) count profile

/-- The complete Required forecast retains every initial profile component. -/
theorem forecast_ge (paths : List (List Int)) (count : Nat) (profile : Profile) : Le profile (forecast paths count profile) :=
  SourceCurrentConstrainedCapRequiredForecast.scan_ge _
    (SourceCurrentConstrainedCapRequiredForecast.plan_ge _) count profile

/-- Worker depth depends only on the original compiled requirement. -/
noncomputable def workerFuel (paths : List (List Int)) : Nat :=
  SourceCurrentRequiredWorkerNumeric.workFuel (SourceEqualityNeeded.build paths)

/-- The initial complete profile supplies one shared reader ceiling. -/
noncomputable def readerFuel (paths : List (List Int)) (count : Nat) (profile : Profile) : Nat :=
  SourceCurrentConstrainedCapRequiredResources.readFuel (forecast paths count profile)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The same actual forest return fits its initial profile and replays at both initial bounds. -/
theorem at_requireAll (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (oldFuel oldRead : Nat) (paths : List (List Int))
    (indices : ∀ path ∈ paths, ∀ index ∈ path, 0 ≤ index)
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll oldFuel oldRead paths values before = .done results after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Values before values) (growth : Grows anchor before)
    (support : SourceCurrentRequiredSupport.ForestSupport unconstrained anchor (SourceEqualityNeeded.build paths) values)
    (profile : Profile) (fits : SourceCurrentConstrainedCapRequiredResources.HeapFits profile before) :
    SourceCurrentConstrainedCapRequiredResources.HeapFits (forecast paths values.length profile) after ∧
      ∀ worker reader, workerFuel paths ≤ worker → readerFuel paths values.length profile ≤ reader →
        SourceEqualityRequiredExecution.requireAll worker reader paths values before = .done results after := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr ⟨oldFuel, oldRead, done⟩
  have valid := SourceEqualityNeeded.build_valid paths
  have nonnegative := SourceEqualityNeededNonnegative.build_nonnegative paths indices
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at graph support valid nonnegative
      have numeric := SourceCurrentConstrainedCapRequiredNumeric.children unconstrained anchor anchorSemantic
        (sizeOf (.node entries : SourceEqualityNeeded.Needed)) entries valid nonnegative graph semantic costs available growth
        support profile fits (Nat.le_refl _)
      refine ⟨?_, ?_⟩
      · simpa only [forecast, compiled] using numeric.1
      · intro worker reader enough readEnough
        have stable := numeric.2 worker reader (by
          unfold workerFuel SourceCurrentRequiredWorkerNumeric.workFuel at enough
          rw [compiled] at enough
          omega) (by simpa only [readerFuel, forecast, compiled] using readEnough)
        simpa only [SourceEqualityRequiredExecution.requireAll, compiled] using stable

/-- Initial primary certificates construct the complete Required return at computed worker and reader bounds. -/
theorem complete (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (profile : Profile) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false before.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results heap final,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before (advanceHeap before heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      Fits (forecast (SourceEqualitySelectedRequired.paths selected) values.length profile) (advanceHeap before heap) ∧
      SourceEqualityRequiredExecution.requireAll (workerFuel (SourceEqualitySelectedRequired.paths selected))
        (readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile)
        (SourceEqualitySelectedRequired.paths selected) values before.native.machine.heap = .done results heap ∧
      (∀ worker reader, workerFuel (SourceEqualitySelectedRequired.paths selected) ≤ worker →
        readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile ≤ reader →
        SourceEqualityRequiredExecution.requireAll worker reader (SourceEqualitySelectedRequired.paths selected)
          values before.native.machine.heap = .done results heap) := by
  obtain ⟨results, heap, final, fuel, readFuel, required, reads, returned, globals, bounded, length, done⟩ :=
    SourceCurrentConstrainedCapSelectedRequiredComplete.complete depth formulas solver inventory unconstrained reaches selected
      values before frame available proper primary caps memos valid
  have support := SourceCurrentRequiredTipSupport.forest_support
    (SourceCurrentRequiredTipSupport.selected_domain frame.ready.semantic available primary)
  have numeric := at_requireAll unconstrained before.native.machine.heap frame.ready.semantic fuel readFuel
    (SourceEqualitySelectedRequired.paths selected) (SourceEqualitySelectedRequired.paths_nonnegative selected)
    values results before.native.machine.heap heap done frame.ready.semantic frame.ready.costs available (grows_refl _)
    support profile (SourceCurrentConstrainedCapRequiredResources.of_checked fits)
  have finalFits := SourceCurrentConstrainedCapRequiredResources.to_checked fits (forecast_ge _ _ _) numeric.1
  exact ⟨results, heap, final, required, reads, returned, globals, bounded, length, finalFits,
    numeric.2 _ _ (Nat.le_refl _) (Nat.le_refl _), numeric.2⟩

/-- The full initial caller retains its exact tables and all laws at the computed Required return. -/
theorem caller (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Caller width)
    (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.checked.native.machine.heap false before.checked.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) :
    ∃ results heap final,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before.checked
        (advanceHeap before.checked heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.checked.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before.checked heap) ∧
      Post formulas solver inventory before (advance before (advanceHeap before.checked heap) before.fourth before.merge) final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      Fits (forecast (SourceEqualitySelectedRequired.paths selected) values.length profile) (advanceHeap before.checked heap) ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).nodeResults = before.nodeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).edgeResults = before.edgeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).fourth = before.fourth ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).merge = before.merge ∧
      SourceEqualityRequiredExecution.requireAll (workerFuel (SourceEqualitySelectedRequired.paths selected))
        (readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile)
        (SourceEqualitySelectedRequired.paths selected) values before.checked.native.machine.heap = .done results heap ∧
      (∀ worker reader, workerFuel (SourceEqualitySelectedRequired.paths selected) ≤ worker →
        readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile ≤ reader →
        SourceEqualityRequiredExecution.requireAll worker reader (SourceEqualitySelectedRequired.paths selected)
          values before.checked.native.machine.heap = .done results heap) := by
  obtain ⟨results, heap, final, fuel, readFuel, required, reads, returned, post, bounded, length,
      nodes, edges, fourth, merged, done⟩ :=
    SourceCurrentConstrainedCapSelectedRequiredComplete.caller depth formulas solver inventory unconstrained reaches
      selected values before memos initial frame available proper primary caps
  have support := SourceCurrentRequiredTipSupport.forest_support
    (SourceCurrentRequiredTipSupport.selected_domain frame.ready.semantic available primary)
  have numeric := at_requireAll unconstrained before.checked.native.machine.heap frame.ready.semantic fuel readFuel
    (SourceEqualitySelectedRequired.paths selected) (SourceEqualitySelectedRequired.paths_nonnegative selected)
    values results before.checked.native.machine.heap heap done frame.ready.semantic frame.ready.costs available (grows_refl _)
    support profile (SourceCurrentConstrainedCapRequiredResources.of_checked fits)
  have finalFits := SourceCurrentConstrainedCapRequiredResources.to_checked fits (forecast_ge _ _ _) numeric.1
  exact ⟨results, heap, final, required, reads, returned, post, bounded, length, finalFits,
    nodes, edges, fourth, merged, numeric.2 _ _ (Nat.le_refl _) (Nat.le_refl _), numeric.2⟩

end MicroCFTA.SourceCurrentConstrainedCapRequiredInitialNumeric
