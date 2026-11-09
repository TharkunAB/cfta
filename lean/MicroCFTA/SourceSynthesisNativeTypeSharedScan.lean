import MicroCFTA.SourceSynthesisNativeTypeGate
import MicroCFTA.SourceSynthesisNativeTypeSeededProfile
import MicroCFTA.SourceCurrentSharedScanCallerNumeric
import MicroCFTA.SourceCurrentConjunctionSharedWorkerGuardArity

/-!
# Type facts at actual shared calls and record scans

The shared call retains its literal checked endpoint on every outcome.
Current physical effects and causal guards derive the conditional Type
store there. Each ordered scan receipt then supplies its actual gates,
seeded query and shared call. The original forest remains fixed.
These laws do not establish scan completion or classify all reached inputs.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSharedScan
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
open SourceCurrentConjunctionClassScan (advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Ready" => SourceSynthesisNativeTypeClosedRequests.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "checkedCall" => SourceCurrentAllocatedSharedConjunctionWorker.call
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
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

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Every shared call outcome derives Type facts at its literal checked return. -/
theorem call (lib : Library) (p h budget : Nat) (query : Node) (before : Checked width) (memo : Memo)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Available before.native.machine.heap query)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib (checkedCall p h budget query before memo).state ∧
      CostHeap (checkedCall p h budget query before memo).state.native.machine.heap ∧
      Extension before.native.machine (checkedCall p h budget query before memo).state.native.machine ∧
      GuardHeap (Origin lib) (checkedCall p h budget query before memo).state.native.machine.heap := by
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic costs
  have effects := (SourceCurrentConjunctionSharedWorkerEffects.call_effects
    p h budget memo query (physical before) physicalReady available).1
  have retained := SourceCurrentConjunctionSharedWorkerGuardArity.call_guard_heap (Origin lib)
    p h budget memo query (physical before) physicalReady guards available
  obtain ⟨next, nextCosts, extension⟩ := advance lib before _ ready effects retained
  have joint := And.intro next (And.intro nextCosts (And.intro extension retained))
  simpa only [SourceCurrentAllocatedSharedConjunctionWorker.call_state,
    SourceCurrentAllocatedSharedConjunctionWorker.call_snapshot,
    SourceCurrentAllocatedQueryMemo.advancePhysical, SourceRecursiveIntersectionThunks.advance] using joint

private theorem query_call (lib : Library)
    {budget p h : Nat} {values : List Node} {paths : EqualityNormalize.Class}
    {before middle later : Checked width} {heap anchor : State Symbol Guard}
    {query : Node} {answer : Bool} {memo saved : Memo} {snapshot : Snapshot}
    (primary : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.native.machine.heap true heap)
    (secondary : SourceCurrentSecondaryTrace.ClassTrace source values paths heap false anchor)
    (seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap (advanceHeap before heap) anchor) query middle)
    (called : checkedCall p h budget query middle memo = .done answer later saved snapshot)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ path ∈ paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib later ∧ CostHeap later.native.machine.heap ∧
      Extension before.native.machine later.native.machine ∧
      GuardHeap (Origin lib) later.native.machine.heap ∧ Values later.native.machine.heap values := by
  obtain ⟨firstReady, firstCosts, first, firstGuards, firstAvailable⟩ :=
    SourceSynthesisNativeTypeGate.primary lib source reaches primary ready costs available guards
  obtain ⟨secondReady, secondCosts, second, secondGuards, secondAvailable⟩ :=
    SourceSynthesisNativeTypeGate.secondary lib source secondary firstReady firstCosts firstAvailable firstGuards
  have signedRoutes : ∀ path ∈ paths.map (List.map Int.ofNat), ForestPath (Origin lib) path values := by
    intro path member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact routes original included
  obtain ⟨middleReady, middleCosts, seededExtension, queryAvailable, _, _, middleGuards⟩ :=
    SourceSynthesisNativeTypeSeededProfile.seeded lib seeded secondReady secondCosts secondAvailable closed signedRoutes secondGuards
  have retained := call lib p h budget query middle memo middleReady middleCosts queryAvailable middleGuards
  rw [called] at retained
  dsimp only [SourceCurrentAllocatedSharedConjunctionWorker.Outcome.state] at retained
  obtain ⟨next, nextCosts, last, afterGuards⟩ := retained
  have extension := ((first.trans second).trans seededExtension).trans last
  exact ⟨next, nextCosts, extension, afterGuards,
    fun value member => extension.available value (available value member)⟩

/-- The literal ordered shared scan retains Type facts and the original available forest. -/
theorem scan (lib : Library)
    {budget : Nat} {values : List Node} {records kept : List SourceEqualityClassOrder.Record}
    {before after : Checked width} {memo saved : Memo} {outcome : Option EqualityNormalize.Class}
    {memos final : Memos}
    (actual : SourceCurrentSharedScanCallerNumeric.ScanReads budget values records before memo outcome kept after saved memos final)
    (ready : Ready lib before) (costs : CostHeap before.native.machine.heap)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (routes : ∀ record ∈ records, ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values)
    (guards : GuardHeap (Origin lib) before.native.machine.heap) :
    Ready lib after ∧ CostHeap after.native.machine.heap ∧
      Extension before.native.machine after.native.machine ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Values after.native.machine.heap values := by
  revert ready costs available closed routes guards
  induction actual with
  | nil =>
      intro ready costs available _ _ guards
      exact ⟨ready, costs, .refl _, guards, available⟩
  | selected firstRead tail ih =>
      intro ready costs available closed routes guards
      obtain ⟨current, currentCosts, first, currentGuards, currentAvailable⟩ :=
        SourceSynthesisNativeTypeGate.primary lib source reaches (by assumption) ready costs available guards
      obtain ⟨next, nextCosts, last, afterGuards, afterAvailable⟩ := ih current currentCosts currentAvailable closed
        (fun record member => routes record (List.mem_cons_of_mem _ member)) currentGuards
      exact ⟨next, nextCosts, first.trans last, afterGuards, afterAvailable⟩
  | skipped firstRead secondRead tail ih =>
      intro ready costs available closed routes guards
      obtain ⟨firstReady, firstCosts, first, firstGuards, firstAvailable⟩ :=
        SourceSynthesisNativeTypeGate.primary lib source reaches (by assumption) ready costs available guards
      obtain ⟨secondReady, secondCosts, second, secondGuards, secondAvailable⟩ :=
        SourceSynthesisNativeTypeGate.secondary lib source (by assumption) firstReady firstCosts firstAvailable firstGuards
      obtain ⟨next, nextCosts, last, afterGuards, afterAvailable⟩ := ih secondReady secondCosts secondAvailable closed
        (fun record member => routes record (List.mem_cons_of_mem _ member)) secondGuards
      exact ⟨next, nextCosts, (first.trans second).trans last, afterGuards, afterAvailable⟩
  | continued firstRead secondRead seededRead called callRead tail ih =>
      intro ready costs available closed routes guards
      obtain ⟨current, currentCosts, first, currentGuards, currentAvailable⟩ :=
        query_call lib (by assumption) (by assumption) (by assumption) called ready costs available closed
          (routes _ List.mem_cons_self) guards
      obtain ⟨next, nextCosts, last, afterGuards, afterAvailable⟩ := ih current currentCosts currentAvailable closed
        (fun record member => routes record (List.mem_cons_of_mem _ member)) currentGuards
      exact ⟨next, nextCosts, first.trans last, afterGuards, afterAvailable⟩
  | stopped firstRead secondRead seededRead called callRead =>
      intro ready costs available closed routes guards
      exact query_call lib (by assumption) (by assumption) (by assumption) called ready costs available closed
        (routes _ List.mem_cons_self) guards

end MicroCFTA.SourceSynthesisNativeTypeSharedScan
