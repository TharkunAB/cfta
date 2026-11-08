import MicroCFTA.SourceSynthesisNativeTypeGate
import MicroCFTA.SourceSynthesisNativeTypeSeededProfile
import MicroCFTA.SourceCurrentConjunctionTupleGuard

/-!
# Type readiness through the actual current class scan

The scan retains its literal warm native and equality-operation states.
Gates and seeded queries derive their causal guard profiles. Actual tuple
decisions retain the same profile. The returned profile supplies the
conditional Mu store for subsequent Type requests. The original forest
stays fixed, so its structural routes and closedness stay fixed.

Completed scan graphs and genuine initial routes remain premises. These
laws do not establish scan completion, all reached operand classifications,
memo answer correctness, finite-word bounds, or native lazy demand order.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeScan
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan (Scan advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

private theorem advance (lib : Library) (before : Checked width) (after : Physical)
    (ready : Ready lib before) (effects : Effects (physical before) after)
    (guards : GuardHeap (Origin lib) after.heap) :
    Ready lib (advancePhysical before after) ∧ CostHeap after.heap ∧
      Extension before.native.machine (advancePhysical before after).native.machine := by
  have previous := SourceCurrentHereditaryNativeUniversalStore.advance (Origin lib) before
    {before.native.machine with heap := after.heap} ready.stored
      (SourceCurrentConstrainedCapGuardNative.stored (Origin lib) after.heap guards)
  have stored : SourceCurrentHereditaryNativeUniversalStore.Stored (Origin lib) (advancePhysical before after) :=
    ⟨previous.constructors, previous.native⟩
  exact ⟨⟨SourceCurrentAllocatedConjunctionMemo.advance_good before after ready.good effects,
      effects.ready.semantic,
      SourceCurrentAllocatedConjunctionMemo.advance_scoped before after ready.scopes,
      SourceCurrentAllocatedConjunctionMemo.advance_idle before after ready.idle, stored⟩,
    effects.ready.costs, SourceCurrentAllocatedQueryMemo.advance_extension before after effects⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- An actual tuple memo call retains the full warm state and causal Type profile. -/
theorem decision (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {memo saved : Memo} {query : Value Symbol Guard} {answer : Bool}
    {before : Checked width} {after : Physical}
    (actual : SourceCurrentConjunctionTupleExecution.Call budget memo query (physical before) answer after saved)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Available before.native.machine.heap query)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib (advancePhysical before after) ∧ CostHeap after.heap ∧
      Extension before.native.machine (advancePhysical before after).native.machine ∧ GuardHeap (Origin lib) after.heap := by
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic costs
  have effects : Effects (physical before) after := by
    cases actual with
    | hit => exact .refl _ physicalReady
    | miss _ part => exact (part.verified physicalReady available formulas solver).1
  have retained := SourceCurrentConjunctionTupleGuard.call (Origin lib) actual physicalReady available guards
  obtain ⟨next, nextCosts, extension⟩ := advance lib before after ready effects retained
  exact ⟨next, nextCosts, extension, retained⟩

private theorem query_decision (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {paths : EqualityNormalize.Class}
    {before middle : Checked width} {heap anchor : State Symbol Guard}
    {query : Value Symbol Guard} {answer : Bool} {later : Physical} {memo saved : Memo}
    (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap true heap)
    (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor)
    (seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap (advanceHeap before heap) anchor) query middle)
    (called : SourceCurrentConjunctionTupleExecution.Call budget memo query (physical middle) answer later saved)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib (advancePhysical middle later) ∧ CostHeap later.heap ∧
      Extension before.native.machine (advancePhysical middle later).native.machine ∧
      GuardHeap (Origin lib) later.heap ∧ Values later.heap values := by
  obtain ⟨firstReady, firstCosts, first, firstGuards, firstAvailable⟩ :=
    SourceSynthesisNativeTypeGate.primary lib unconstrained reaches primary ready costs available guards
  obtain ⟨secondReady, secondCosts, second, secondGuards, secondAvailable⟩ :=
    SourceSynthesisNativeTypeGate.secondary lib unconstrained secondary firstReady firstCosts firstAvailable firstGuards
  have signedRoutes : ∀ path ∈ paths.map (List.map Int.ofNat), ForestPath (Origin lib) path values := by
    intro path member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact routes original included
  obtain ⟨middleReady, middleCosts, seededExtension, queryAvailable, _, _, middleGuards⟩ :=
    SourceSynthesisNativeTypeSeededProfile.seeded lib seeded secondReady secondCosts secondAvailable closed signedRoutes secondGuards
  obtain ⟨next, nextCosts, last, afterGuards⟩ := decision lib formulas solver called middleReady middleCosts queryAvailable middleGuards
  have extension := ((first.trans second).trans seededExtension).trans last
  exact ⟨next, nextCosts, extension, afterGuards,
    fun value member => extension.available value (available value member)⟩

/-- Every reached scan branch derives Type readiness at its actual warm return. -/
theorem scan (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {classes selected : EqualityNormalize.Constraints}
    {before after : Checked width} {memo saved : Memo} {outcome : Option EqualityNormalize.Class}
    (actual : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ paths ∈ classes, ∀ path ∈ paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧ Extension before.native.machine after.native.machine ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Values after.native.machine.heap values := by
  revert ready costs available closed routes guards
  induction actual with
  | nil =>
      intro ready costs available _ _ guards
      exact ⟨ready, costs, .refl _, guards, available⟩
  | selected primary rest ih =>
      intro ready costs available closed routes guards
      obtain ⟨current, currentCosts, first, currentGuards, currentAvailable⟩ :=
        SourceSynthesisNativeTypeGate.primary lib unconstrained reaches primary ready costs available guards
      obtain ⟨next, nextCosts, last, afterGuards, afterAvailable⟩ := ih current currentCosts currentAvailable closed
        (fun paths member => routes paths (List.mem_cons_of_mem _ member)) currentGuards
      exact ⟨next, nextCosts, first.trans last, afterGuards, afterAvailable⟩
  | skipped primary secondary rest ih =>
      intro ready costs available closed routes guards
      obtain ⟨firstReady, firstCosts, first, firstGuards, firstAvailable⟩ :=
        SourceSynthesisNativeTypeGate.primary lib unconstrained reaches primary ready costs available guards
      obtain ⟨secondReady, secondCosts, second, secondGuards, secondAvailable⟩ :=
        SourceSynthesisNativeTypeGate.secondary lib unconstrained secondary firstReady firstCosts firstAvailable firstGuards
      obtain ⟨next, nextCosts, last, afterGuards, afterAvailable⟩ := ih secondReady secondCosts secondAvailable closed
        (fun paths member => routes paths (List.mem_cons_of_mem _ member)) secondGuards
      exact ⟨next, nextCosts, (first.trans second).trans last, afterGuards, afterAvailable⟩
  | continued primary secondary seeded called rest ih =>
      intro ready costs available closed routes guards
      obtain ⟨current, currentCosts, first, currentGuards, currentAvailable⟩ :=
        query_decision lib formulas solver primary secondary seeded called ready costs available closed
          (routes _ List.mem_cons_self) guards
      obtain ⟨next, nextCosts, last, afterGuards, afterAvailable⟩ := ih current currentCosts currentAvailable closed
        (fun paths member => routes paths (List.mem_cons_of_mem _ member)) currentGuards
      exact ⟨next, nextCosts, first.trans last, afterGuards, afterAvailable⟩
  | stopped primary secondary seeded called =>
      intro ready costs available closed routes guards
      exact query_decision lib formulas solver primary secondary seeded called ready costs available closed
        (routes _ List.mem_cons_self) guards

end MicroCFTA.SourceSynthesisNativeTypeScan
