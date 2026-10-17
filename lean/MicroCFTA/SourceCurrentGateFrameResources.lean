import MicroCFTA.SourceCurrentGateGuard
import MicroCFTA.SourceCurrentPrimaryGateNumericReplay
import MicroCFTA.SourceCurrentSecondaryGateResources
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame
import MicroCFTA.SourceCurrentConstrainedCapRequiredResources

/-!
# Complete initial class gates with query Frames

Original paths and constructor resources bound both source gate modes.
Each mode constructs its own actual graph and retains the same inventory,
causal guard observations, native cells, and full query Frame.
No closed-input or finite-cap premise is added.
-/
namespace MicroCFTA.SourceCurrentGateFrameResources
open Cache InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConjunctionClassScan (advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "scalar" => SourceCurrentConstrainedCapEditForecast.scalar
local notation "classBound" => SourceCurrentPrimaryGateResources.classBound
local notation "classFuel" => SourceCurrentPrimaryGateResources.classFuel
variable {width : Nat}

/-- The original class paths bound the returned heap and retain the native domain supply. -/
def forecast (paths : Class) (profile : Profile) : Profile :=
  let bound := classBound paths (scalar profile)
  ⟨bound, bound, profile.domains, bound⟩

/-- The class forecast retains each initial resource component. -/
theorem forecast_ge (paths : Class) (profile : Profile) : Le profile (forecast paths profile) := by
  have enough := SourceCurrentPrimaryGateResources.classBound_ge paths (scalar profile)
  exact ⟨Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile) enough,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile) enough, Nat.le_refl _,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile) enough⟩

/-- Increasing initial resources retains the same class forecast. -/
theorem forecast_mono (paths : Class) {first last : Profile} (increase : Le first last) :
    Le (forecast paths first) (forecast paths last) := by
  have enough := SourceCurrentPrimaryGateResources.classBound_mono paths
    (SourceCurrentConstrainedCapEditForecast.scalar_mono increase)
  exact ⟨enough, enough, increase.2.2.1, enough⟩

/-- Both source gate modes share the fuel from the original class and entry profile. -/
def workerFuel (paths : Class) (profile : Profile) : Nat := classFuel paths (scalar profile)

/-- Increasing the initial profile retains the shared worker bound. -/
theorem workerFuel_mono (paths : Class) {first last : Profile} (increase : Le first last) :
    workerFuel paths first ≤ workerFuel paths last :=
  SourceCurrentPrimaryGateResources.classFuel_mono paths (SourceCurrentConstrainedCapEditForecast.scalar_mono increase)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The initial primary class constructs its exact return with full Frame and forecast Fits. -/
theorem primary (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : Class) (before : Checked width) (frame : Frame formulas solver inventory before)
    (profile : Profile) (fits : Fits profile before) (available : Values before.native.machine.heap values) :
    ∃ answer heap,
      EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap answer heap ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      Fits (forecast paths profile) (advanceHeap before heap) ∧ Values heap values ∧
      SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
        (SourceCurrentAllocatedNativeEffects.physical (advanceHeap before heap)) ∧
      ∀ fuel, workerFuel paths profile ≤ fuel →
        SourceCurrentMuEndpoint.classMeets true unconstrained reaches fuel values paths before.native.machine.heap =
          .done (some answer) heap := by
  classical
  have initialFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  obtain ⟨answer, heap, actual, _semantic, _costs, kept, retained, bounded, stable⟩ :=
    SourceCurrentPrimaryGateNumericReplay.class_complete unconstrained reaches values paths before.native.machine.heap
      frame.ready.semantic frame.ready.costs available (scalar profile) initialFits
  have effects := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches actual frame.ready available
  have guards := SourceCurrentGateGuard.primary Plain unconstrained reaches actual frame.ready.semantic frame.ready.costs
    available frame.context.guards
  have extension : SourceRecursiveIntersectionKernel.Extension before.native.machine (advanceHeap before heap).native.machine :=
    ⟨kept.growth, kept.history, extends_refl _⟩
  have returned := SourceCurrentConstrainedCapOperandFrame.advance frame effects.1 extension rfl rfl guards
  refine ⟨answer, heap, actual, returned, ⟨bounded.nodes, bounded.edges, fits.domains, bounded.stored⟩,
    retained, effects.2.1, ?_⟩
  intro fuel enough
  simpa only [SourceCurrentMuEndpoint.primary_class] using stable fuel enough

/-- The initial secondary class constructs the same full invariants at its original numeric bounds. -/
theorem secondary (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : Class) (before : Checked width) (frame : Frame formulas solver inventory before)
    (profile : Profile) (fits : Fits profile before) (available : Values before.native.machine.heap values) :
    ∃ answer heap,
      SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap answer heap ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      Fits (forecast paths profile) (advanceHeap before heap) ∧ Values heap values ∧
      SourceCurrentConjunctionRowsAllocation.Effects (SourceCurrentAllocatedNativeEffects.physical before)
        (SourceCurrentAllocatedNativeEffects.physical (advanceHeap before heap)) ∧
      ∀ fuel, workerFuel paths profile ≤ fuel →
        SourceCurrentMuEndpoint.classMeets false unconstrained reaches fuel values paths before.native.machine.heap =
          .done (some answer) heap := by
  classical
  have initialFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  obtain ⟨answer, heap, actual, _semantic, _costs, kept, retained, bounded, stable⟩ :=
    SourceCurrentSecondaryGateResources.class_complete unconstrained values paths before.native.machine.heap
      frame.ready.semantic frame.ready.costs available (scalar profile) initialFits
  have effects := SourceCurrentConjunctionClassScan.secondary_effects unconstrained actual frame.ready available
  have guards := SourceCurrentGateGuard.secondary Plain unconstrained actual frame.ready.semantic frame.ready.costs
    available frame.context.guards
  have extension : SourceRecursiveIntersectionKernel.Extension before.native.machine (advanceHeap before heap).native.machine :=
    ⟨kept.growth, kept.history, extends_refl _⟩
  have returned := SourceCurrentConstrainedCapOperandFrame.advance frame effects.1 extension rfl rfl guards
  refine ⟨answer, heap, actual, returned, ⟨bounded.nodes, bounded.edges, fits.domains, bounded.stored⟩,
    retained, effects.2.1, ?_⟩
  intro fuel enough
  simpa only [SourceCurrentSecondaryTrace.actual_current_class_eq] using stable fuel enough

end MicroCFTA.SourceCurrentGateFrameResources
