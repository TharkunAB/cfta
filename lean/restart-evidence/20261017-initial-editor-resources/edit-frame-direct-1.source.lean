import MicroCFTA.SourceCurrentConstrainedCapOperandFrame
import MicroCFTA.SourceCurrentConstrainedCapMixedEditStoreEffects
import MicroCFTA.SourceCurrentConstrainedCapTargetForecast
import MicroCFTA.SourceCurrentProjectionUnionResources

/-!
# Query frames through actual shared edit heap work

Constructor requests use an initial list-width bound. Recursive Head uses
its actual read and rebuild. Each result retains the same inventory, target
slots, Merge table, and complete query frame at the returned checked state.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapEditFrame
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapTargetForecast (scalar)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects

/-- A constructor forecast bounds the full heap and keeps the domain counter. -/
def constructorProfile (count : Nat) (profile : Profile) : Profile :=
  let bound := SourceCurrentMemoMergeResourceControl.primitiveGrowth count (scalar profile)
  ⟨bound, bound, profile.domains, bound⟩

/-- Head exposure forecasts its complete read and final node constructor. -/
def headProfile (profile : Profile) : Profile :=
  let bound := SourceCurrentProjectionUnionResources.headGrowth (scalar profile)
  ⟨bound, bound, profile.domains, bound⟩

/-- The shared Head certificate uses the reader fuel at its final scalar bound. -/
def headFuel (profile : Profile) : Nat :=
  SourceCurrentProjectionUnionResources.readFuel
    (SourceCurrentProjectionUnionResources.headGrowth (scalar profile))

/-- Constructor work retains every initial profile component. -/
theorem constructorProfile_ge (count : Nat) (profile : Profile) : Le profile (constructorProfile count profile) := by
  have enough := SourceCurrentMemoMergeResourceControl.primitiveGrowth_ge count (scalar profile)
  exact ⟨Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile) enough,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile) enough, Nat.le_refl _,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile) enough⟩

/-- Larger initial profiles retain the same constructor forecast. -/
theorem constructorProfile_mono (count : Nat) {first last : Profile} (increase : Le first last) :
    Le (constructorProfile count first) (constructorProfile count last) := by
  have bounds := SourceCurrentMemoMergeResourceControl.primitiveGrowth_mono (Nat.le_refl count)
    (SourceCurrentConstrainedCapTargetForecast.scalar_mono increase)
  exact ⟨bounds, bounds, increase.2.2.1, bounds⟩

/-- A larger initial list-width bound retains the constructor forecast. -/
theorem constructorProfile_count_mono {first last : Nat} (increase : first ≤ last) (profile : Profile) :
    Le (constructorProfile first profile) (constructorProfile last profile) := by
  have bounds := SourceCurrentMemoMergeResourceControl.primitiveGrowth_mono increase (Nat.le_refl (scalar profile))
  exact ⟨bounds, bounds, Nat.le_refl _, bounds⟩

/-- Head exposure retains every initial profile component. -/
theorem headProfile_ge (profile : Profile) : Le profile (headProfile profile) := by
  have enough := SourceCurrentProjectionUnionResources.headGrowth_ge (scalar profile)
  exact ⟨Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile) enough,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile) enough, Nat.le_refl _,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile) enough⟩

/-- Larger initial profiles retain the complete Head forecast. -/
theorem headProfile_mono {first last : Profile} (increase : Le first last) :
    Le (headProfile first) (headProfile last) := by
  have bounds := SourceCurrentProjectionUnionResources.headGrowth_mono
    (SourceCurrentConstrainedCapTargetForecast.scalar_mono increase)
  exact ⟨bounds, bounds, increase.2.2.1, bounds⟩

/-- Larger initial profiles retain the shared Head reader fuel. -/
theorem headFuel_mono {first last : Profile} (increase : Le first last) : headFuel first ≤ headFuel last :=
  SourceCurrentProjectionUnionResources.readFuel_mono (SourceCurrentProjectionUnionResources.headGrowth_mono
    (SourceCurrentConstrainedCapTargetForecast.scalar_mono increase))

variable {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : Heap} {before : SharedState width}

private theorem scalar_fits (profile : Profile) (fits : Fits profile before.checked) :
    SourceCurrentMemoMergeResourceControl.Fits (scalar profile) before.checked.native.machine.heap :=
  ⟨fits.stored.mono (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile),
    Nat.le_trans fits.nodes (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile),
    Nat.le_trans fits.edges (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile), Nat.zero_le _⟩

private theorem heap_fits (profile : Profile) (bound : Nat) (heap : Heap)
    (fits : Fits profile before.checked) (returned : SourceCurrentMemoMergeResourceControl.Fits bound heap) :
    Fits ⟨bound, bound, profile.domains, bound⟩ (advanceHeap before heap).checked :=
  ⟨returned.nodes, returned.edges, fits.domains, returned.stored⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual node work retains the full frame, shared stores, and initial numeric forecast. -/
theorem node (profile : Profile) (count : Nat) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (ready : Ready formulas solver inventory record originals base before)
    (rows : List (EdgeValue Symbol Guard)) (resident : Edges before.checked.native.machine.heap rows)
    (length : rows.length ≤ count) (stored : Stored record originals before) :
    let actual := run (makeNode rows) before.checked.native.machine.heap
    Frame formulas solver inventory (advanceHeap before actual.2).checked ∧
      Fits (constructorProfile count profile) (advanceHeap before actual.2).checked ∧
      Stored record originals (advanceHeap before actual.2) ∧
      Ready formulas solver inventory record originals base (advanceHeap before actual.2) ∧
      Effects (physical before.checked) (physical (advanceHeap before actual.2).checked) ∧
      Available actual.2 actual.1 := by
  have returned := SourceCurrentConstrainedCapMixedEditStoreEffects.node ready rows resident stored
  have resources := SourceCurrentMemoMergeResourceControl.node rows before.checked.native.machine.heap
    (scalar profile) count (scalar_fits profile fits) resident length
  have current := SourceCurrentConstrainedCapOperandFrame.advance frame returned.2.1.checked
    (SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ returned.2.2.1) rfl rfl
    returned.1.current.1.guards
  exact ⟨current, heap_fits profile _ _ fits resources.1, returned⟩

/-- Actual raw edge work retains the original field, exact children, and full frame. -/
theorem edge (profile : Profile) (count : Nat) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (ready : Ready formulas solver inventory record originals base before)
    (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations guard)
    (available : Values before.checked.native.machine.heap children) (length : children.length ≤ count)
    (stored : Stored record originals before) :
    let actual := run (makeEdge symbol guard children) before.checked.native.machine.heap
    Frame formulas solver inventory (advanceHeap before actual.2).checked ∧
      Fits (constructorProfile count profile) (advanceHeap before actual.2).checked ∧
      Stored record originals (advanceHeap before actual.2) ∧
      Ready formulas solver inventory record originals base (advanceHeap before actual.2) ∧
      Effects (physical before.checked) (physical (advanceHeap before actual.2).checked) ∧
      InternedEdgeResidency.EdgeResident actual.2 actual.1 ∧ actual.1.children = children := by
  have returned := SourceCurrentConstrainedCapMixedEditStoreEffects.edge ready symbol guard children field available stored
  have resources := SourceCurrentMemoMergeResourceControl.edge symbol guard children before.checked.native.machine.heap
    (scalar profile) count (scalar_fits profile fits) available length
  have current := SourceCurrentConstrainedCapOperandFrame.advance frame returned.2.1.checked
    (SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ returned.2.2.1) rfl rfl
    returned.1.current.1.guards
  exact ⟨current, heap_fits profile _ _ fits resources.1, returned⟩

/-- The SAME successful recursive Head retains the full frame and its computed reader certificate. -/
theorem head (profile : Profile) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (ready : Ready formulas solver inventory record originals base before)
    {input exposed : Value Symbol Guard} {heap : Heap}
    (actual : SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (stored : Stored record originals before) :
    Frame formulas solver inventory (advanceHeap before heap).checked ∧
      Fits (headProfile profile) (advanceHeap before heap).checked ∧
      Stored record originals (advanceHeap before heap) ∧
      Ready formulas solver inventory record originals base (advanceHeap before heap) ∧
      Effects (physical before.checked) (physical (advanceHeap before heap).checked) ∧
      Available heap exposed ∧ exposed.free = [] ∧
      SourceCurrentProjectionNumericReplay.HeadReady (headFuel profile) actual := by
  have returned := SourceCurrentAllocatedSharedEditEffects.head_physical ready actual available
  have guards := SourceCurrentConstrainedCapProjectionGuard.head Plain actual frame.ready.semantic frame.ready.costs
    available frame.context.guards
  have current := SourceCurrentConstrainedCapOperandFrame.advance frame returned.1.checked
    (SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ returned.2.1) rfl rfl guards
  have resources := SourceCurrentProjectionUnionResources.head actual (scalar profile)
    frame.ready.semantic frame.ready.costs available closed (scalar_fits profile fits)
  have shared := SourceCurrentConstrainedCapMixedShared.advance_stored record originals before _ stored
    (SourceCurrentConstrainedCapOperandFrame.current current)
  exact ⟨current, heap_fits profile _ _ fits resources.2.1, shared, returned.1, returned.2.1,
    resources.2.2⟩

end MicroCFTA.SourceCurrentConstrainedCapEditFrame
