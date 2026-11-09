import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedPrimaryCompletion
import MicroCFTA.SourceCurrentAllocatedProbeGates

/-!
# Current caller postconditions for the actual Scan gates

Each gate uses its exact reached trace and ordered memo reads. The returned
caller retains the original inventory, fourth memo and merge memo. Seeded
query postconditions use the existing SeededCallerNumeric.of_receipt law.
-/
namespace MicroCFTA.SourceCurrentSharedScanCallerSteps
open Cache EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionClassScan (Ready advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "advance" => SourceCurrentAllocatedPartialState.advance
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
  (solver : SourceGuards.Entailment FullSyntax.Formula)

omit [DecidableEq Symbol] in
private theorem gate_post {inventory : Inventory} {before : Caller width}
    {heap : State Symbol Guard} {memos final : Memos}
    (initial : Context formulas solver inventory before memos)
    (ready : Ready (advanceHeap before.checked heap))
    (effects : SourceCurrentConjunctionRowsAllocation.Effects
      (physical before.checked) (physical (advanceHeap before.checked heap)))
    (globals : EndpointMemoGateTrace.Valid heap final)
    (probes : InternedFreshOrdinaryProbeHeap.Heap heap) :
    Post formulas solver inventory before
      (advance before (advanceHeap before.checked heap) before.fourth before.merge) final := by
  have admitted := initial.admitted.advance ⟨heap, before.checked.operations⟩
    (SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ effects)
  exact ⟨⟨ready, admitted,
    initial.sound.advance formulas solver _ before.fourth before.merge effects,
    initial.stored.grows effects.keeps, initial.covered,
    SourceCurrentEmptinessMemo.grows formulas solver effects.keeps before.fourth initial.correct,
    globals, probes⟩, effects, Cache.extends_refl _, fun _ _ found => found⟩

/-- An actual primary trace derives its own ordered reads and full returned caller. -/
theorem primary_post {inventory : Inventory} {before : Caller width} {memos : Memos}
    {values : List (Value Symbol Guard)} {paths : Class} {answer : Bool} {heap : State Symbol Guard}
    (actual : EndpointStatefulGateTrace.ClassTrace source reaches values paths
      before.checked.native.machine.heap answer heap)
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values) :
    ∃ final, SourceCurrentAllocatedPrimaryReads.ClassReads actual memos final ∧
      Post formulas solver inventory before
        (advance before (advanceHeap before.checked heap) before.fourth before.merge) final := by
  have effects := SourceCurrentConjunctionClassScan.primary_effects source reaches actual initial.ready available
  have probes := (SourceCurrentAllocatedProbeGates.Primary.class_effects source reaches actual
    initial.ready.semantic initial.ready.costs available initial.probes).2.2.2
  obtain ⟨final, reads, kept⟩ := SourceCurrentAllocatedPrimaryReads.lift_class values paths
    before.checked.native.machine.heap answer heap actual
    (SourceCurrentClassGateCompletion.gate_ready initial.ready.semantic initial.ready.costs)
    available memos initial.globals
  exact ⟨final, reads, gate_post formulas solver initial effects.1 effects.2.1 kept.valid probes⟩

/-- An actual secondary trace derives its own ordered reads and full returned caller. -/
theorem secondary_post {inventory : Inventory} {before : Caller width} {memos : Memos}
    {values : List (Value Symbol Guard)} {paths : Class} {answer : Bool} {heap : State Symbol Guard}
    (actual : SourceCurrentSecondaryTrace.ClassTrace source values paths
      before.checked.native.machine.heap answer heap)
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values) :
    ∃ final, SourceCurrentSecondaryMemos.ClassReads actual memos final ∧
      Post formulas solver inventory before
        (advance before (advanceHeap before.checked heap) before.fourth before.merge) final := by
  have effects := SourceCurrentConjunctionClassScan.secondary_effects source actual initial.ready available
  have probes := (SourceCurrentAllocatedProbeGates.Secondary.class_effects source actual
    initial.ready.semantic initial.ready.costs available initial.probes).2.2.2
  obtain ⟨final, reads, kept⟩ := SourceCurrentSecondaryMemos.lift_class values paths
    before.checked.native.machine.heap answer heap actual
    (SourceCurrentClassGateCompletion.gate_ready initial.ready.semantic initial.ready.costs)
    available memos initial.globals
  exact ⟨final, reads, gate_post formulas solver initial effects.1 effects.2.1 kept.valid probes⟩

end MicroCFTA.SourceCurrentSharedScanCallerSteps
