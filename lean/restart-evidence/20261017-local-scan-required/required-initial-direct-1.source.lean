import MicroCFTA.SourceCurrentConstrainedCapRequiredNumeric
import MicroCFTA.SourceCurrentRequiredGuard
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame
import MicroCFTA.SourceCurrentConjunctionRequiredGlobalMemos
import MicroCFTA.SourceCurrentAllocatedProbeRequired
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

/-!
# Complete selected Required from initial numeric resources

Original primary certificates construct the actual Required graph.
The same return fits the forecast from the initial trie and forest count.
Both worker and reader bounds are fixed from those original inputs.
The full query Frame, caller Post, and exact tables remain tied to it.
No cap or whole-forest closedness premise is required.
-/
namespace MicroCFTA.SourceCurrentRequiredInitialNumeric
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
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "advance" => SourceCurrentAllocatedPartialState.advance
variable {width : Nat}

/-- The initial trie and literal forest count fix the complete Required profile. -/
noncomputable def forecast (paths : List (List Int)) (count : Nat) (profile : Profile) : Profile :=
  SourceCurrentConstrainedCapRequiredInitialNumeric.forecast paths count profile

/-- The complete Required forecast retains every initial profile component. -/
theorem forecast_ge (paths : List (List Int)) (count : Nat) (profile : Profile) : Le profile (forecast paths count profile) :=
  SourceCurrentConstrainedCapRequiredInitialNumeric.forecast_ge paths count profile

/-- Worker depth depends only on the original compiled requirement. -/
noncomputable def workerFuel (paths : List (List Int)) : Nat :=
  SourceCurrentConstrainedCapRequiredInitialNumeric.workerFuel paths

/-- The initial complete profile supplies one shared reader ceiling. -/
noncomputable def readerFuel (paths : List (List Int)) (count : Nat) (profile : Profile) : Nat :=
  SourceCurrentConstrainedCapRequiredInitialNumeric.readerFuel paths count profile

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial primary certificates construct Required, its full Frame, global effect, and guard observations. -/
private theorem qualitative
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false before.native.machine.heap)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results heap final fuel readFuel,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before
        (advanceHeap before heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
      results.length = values.length ∧
      SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values before.native.machine.heap = .done results heap := by
  obtain ⟨results, heap, required⟩ := SourceCurrentConjunctionRequired.required_complete
    formulas solver inventory unconstrained reaches selected values before frame.ready frame.admitted available proper primary
  obtain ⟨fuel, readFuel, stable⟩ := required.stable
  have done := stable fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨final, reads, finalValid, retained, query⟩ := SourceCurrentRequiredQueryMemos.requireAll_memos
    fuel readFuel (SourceEqualitySelectedRequired.paths selected) values results before.native.machine.heap heap done
      frame.ready.semantic frame.ready.costs available memos valid
  have produced := SourceCurrentRequiredGuard.requireAll Plain reads frame.ready.semantic
    frame.ready.costs available frame.context.guards
  have returned := SourceCurrentConstrainedCapOperandFrame.advance frame required.ready required.extension
    required.nodes required.edges produced.1
  exact ⟨results, heap, final, fuel, readFuel, required, reads, returned,
    ⟨required.effects.keeps, required.ready.semantic, required.ready.costs, finalValid, retained, query⟩,
    produced.2, done⟩

/-- The constructed Required prefix retains the complete caller and both unchanged outer tables. -/
private theorem qualitative_caller
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Caller width)
    (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.checked.native.machine.heap false before.checked.native.machine.heap) :
    ∃ results heap final fuel readFuel,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before.checked
        (advanceHeap before.checked heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.checked.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before.checked heap) ∧
      Post formulas solver inventory before (advance before (advanceHeap before.checked heap) before.fourth before.merge) final ∧
      results.length = values.length ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).nodeResults = before.nodeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).edgeResults = before.edgeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).fourth = before.fourth ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).merge = before.merge ∧
      SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values before.checked.native.machine.heap = .done results heap := by
  obtain ⟨results, heap, final, fuel, readFuel, required, reads, returned, globals, length, done⟩ :=
    qualitative formulas solver inventory unconstrained reaches selected values before.checked frame available
      proper primary memos initial.globals
  have probes := SourceCurrentAllocatedProbeRequired.requireAll fuel readFuel
    (SourceEqualitySelectedRequired.paths selected) values results before.checked.native.machine.heap heap done
    initial.ready.semantic initial.ready.costs initial.probes available
  have post : Post formulas solver inventory before
      (advance before (advanceHeap before.checked heap) before.fourth before.merge) final :=
    ⟨⟨required.ready, required.admitted,
      initial.sound.advance formulas solver _ before.fourth before.merge required.effects,
      initial.stored.grows required.effects.keeps, initial.covered,
      SourceCurrentEmptinessMemo.grows formulas solver required.effects.keeps before.fourth initial.correct,
      globals.valid, probes.2.2.2.1⟩, required.effects, extends_refl _, fun _ _ found => found⟩
  exact ⟨results, heap, final, fuel, readFuel, required, reads, returned, post,
    length, rfl, rfl, rfl, rfl, done⟩


/-- Initial primary certificates construct the complete Required return at computed worker and reader bounds. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (profile : Profile) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false before.native.machine.heap)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results heap final,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before (advanceHeap before heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
      results.length = values.length ∧
      Fits (forecast (SourceEqualitySelectedRequired.paths selected) values.length profile) (advanceHeap before heap) ∧
      SourceEqualityRequiredExecution.requireAll (workerFuel (SourceEqualitySelectedRequired.paths selected))
        (readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile)
        (SourceEqualitySelectedRequired.paths selected) values before.native.machine.heap = .done results heap ∧
      (∀ worker reader, workerFuel (SourceEqualitySelectedRequired.paths selected) ≤ worker →
        readerFuel (SourceEqualitySelectedRequired.paths selected) values.length profile ≤ reader →
        SourceEqualityRequiredExecution.requireAll worker reader (SourceEqualitySelectedRequired.paths selected)
          values before.native.machine.heap = .done results heap) := by
  obtain ⟨results, heap, final, fuel, readFuel, required, reads, returned, globals, length, done⟩ :=
    qualitative formulas solver inventory unconstrained reaches selected
      values before frame available proper primary memos valid
  have support := SourceCurrentRequiredTipSupport.forest_support
    (SourceCurrentRequiredTipSupport.selected_domain frame.ready.semantic available primary)
  have numeric := SourceCurrentConstrainedCapRequiredInitialNumeric.at_requireAll unconstrained before.native.machine.heap frame.ready.semantic fuel readFuel
    (SourceEqualitySelectedRequired.paths selected) (SourceEqualitySelectedRequired.paths_nonnegative selected)
    values results before.native.machine.heap heap done frame.ready.semantic frame.ready.costs available (grows_refl _)
    support profile (SourceCurrentConstrainedCapRequiredResources.of_checked fits)
  have finalFits := SourceCurrentConstrainedCapRequiredResources.to_checked fits (forecast_ge _ _ _) numeric.1
  exact ⟨results, heap, final, required, reads, returned, globals, length, finalFits,
    numeric.2 _ _ (Nat.le_refl _) (Nat.le_refl _), numeric.2⟩

/-- The full initial caller retains its exact tables and all laws at the computed Required return. -/
theorem caller
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Caller width)
    (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.checked.native.machine.heap false before.checked.native.machine.heap) :
    ∃ results heap final,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before.checked
        (advanceHeap before.checked heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.checked.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before.checked heap) ∧
      Post formulas solver inventory before (advance before (advanceHeap before.checked heap) before.fourth before.merge) final ∧
      results.length = values.length ∧
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
  obtain ⟨results, heap, final, fuel, readFuel, required, reads, returned, post, length,
      nodes, edges, fourth, merged, done⟩ :=
    qualitative_caller formulas solver inventory unconstrained reaches
      selected values before memos initial frame available proper primary
  have support := SourceCurrentRequiredTipSupport.forest_support
    (SourceCurrentRequiredTipSupport.selected_domain frame.ready.semantic available primary)
  have numeric := SourceCurrentConstrainedCapRequiredInitialNumeric.at_requireAll unconstrained before.checked.native.machine.heap frame.ready.semantic fuel readFuel
    (SourceEqualitySelectedRequired.paths selected) (SourceEqualitySelectedRequired.paths_nonnegative selected)
    values results before.checked.native.machine.heap heap done frame.ready.semantic frame.ready.costs available (grows_refl _)
    support profile (SourceCurrentConstrainedCapRequiredResources.of_checked fits)
  have finalFits := SourceCurrentConstrainedCapRequiredResources.to_checked fits (forecast_ge _ _ _) numeric.1
  exact ⟨results, heap, final, required, reads, returned, post, length, finalFits,
    nodes, edges, fourth, merged, numeric.2 _ _ (Nat.le_refl _) (Nat.le_refl _), numeric.2⟩

end MicroCFTA.SourceCurrentRequiredInitialNumeric
