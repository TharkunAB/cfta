import MicroCFTA.SourceCurrentConstrainedCapEditFrame
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
import MicroCFTA.SourceCurrentAllocatedSharedEditEffects

/-!
# Full query Frames through uncapped editor constructors and Head

Actual physical effects retain the existing shared receipts and Merge laws.
Causal guard observations supply the same returned query Frame.
No finite cap or mixed annotation store is required.
-/
namespace MicroCFTA.SourceCurrentEditFrame
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
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects

export SourceCurrentConstrainedCapEditFrame
  (constructorProfile headProfile headFuel constructorProfile_ge constructorProfile_mono
    constructorProfile_count_mono headProfile_ge headProfile_mono headFuel_mono)

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

/-- Actual node work retains the full Frame, physical effects, and initial numeric forecast. -/
theorem node (profile : Profile) (count : Nat) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (ready : Ready formulas solver inventory record originals base before)
    (rows : List (EdgeValue Symbol Guard)) (resident : Edges before.checked.native.machine.heap rows)
    (length : rows.length ≤ count) :
    let actual := run (makeNode rows) before.checked.native.machine.heap
    Frame formulas solver inventory (advanceHeap before actual.2).checked ∧
      Fits (constructorProfile count profile) (advanceHeap before actual.2).checked ∧
      Ready formulas solver inventory record originals base (advanceHeap before actual.2) ∧
      Effects (physical before.checked) (physical (advanceHeap before actual.2).checked) ∧
      Available actual.2 actual.1 := by
  have returned := SourceCurrentAllocatedSharedEditEffects.node_physical ready rows resident
  have guards := SourceCurrentConstrainedCapGuardHeap.preserve Plain before.checked.native.machine.heap _
    frame.context.guards (InternedShallowHeap.makeNode_noNewMu rows before.checked.native.machine.heap)
  have resources := SourceCurrentMemoMergeResourceControl.node rows before.checked.native.machine.heap
    (scalar profile) count (scalar_fits profile fits) resident length
  have current := SourceCurrentConstrainedCapOperandFrame.advance frame returned.1.checked
    (SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ returned.2.1) rfl rfl
    guards
  exact ⟨current, heap_fits profile _ _ fits resources.1, returned⟩

/-- Actual raw edge work retains the original field, exact children, and full frame. -/
theorem edge (profile : Profile) (count : Nat) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (ready : Ready formulas solver inventory record originals base before)
    (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations guard)
    (available : Values before.checked.native.machine.heap children) (length : children.length ≤ count)
    :
    let actual := run (makeEdge symbol guard children) before.checked.native.machine.heap
    Frame formulas solver inventory (advanceHeap before actual.2).checked ∧
      Fits (constructorProfile count profile) (advanceHeap before actual.2).checked ∧
      Ready formulas solver inventory record originals base (advanceHeap before actual.2) ∧
      Effects (physical before.checked) (physical (advanceHeap before actual.2).checked) ∧
      InternedEdgeResidency.EdgeResident actual.2 actual.1 ∧ actual.1.children = children := by
  have returned := SourceCurrentAllocatedSharedEditEffects.edge_physical ready symbol guard children field available
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain
      (run (makeEdge symbol guard children) before.checked.native.machine.heap).2 := frame.context.guards
  have resources := SourceCurrentMemoMergeResourceControl.edge symbol guard children before.checked.native.machine.heap
    (scalar profile) count (scalar_fits profile fits) available length
  have current := SourceCurrentConstrainedCapOperandFrame.advance frame returned.1.checked
    (SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ returned.2.1) rfl rfl
    guards
  exact ⟨current, heap_fits profile _ _ fits resources.1, returned⟩

/-- The SAME successful recursive Head retains the full frame and its computed reader certificate. -/
theorem head (profile : Profile) (frame : Frame formulas solver inventory before.checked)
    (fits : Fits profile before.checked) (ready : Ready formulas solver inventory record originals base before)
    {input exposed : Value Symbol Guard} {heap : Heap}
    (actual : SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    :
    Frame formulas solver inventory (advanceHeap before heap).checked ∧
      Fits (headProfile profile) (advanceHeap before heap).checked ∧
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
  exact ⟨current, heap_fits profile _ _ fits resources.2.1, returned.1, returned.2.1,
    resources.2.2⟩

end MicroCFTA.SourceCurrentEditFrame
