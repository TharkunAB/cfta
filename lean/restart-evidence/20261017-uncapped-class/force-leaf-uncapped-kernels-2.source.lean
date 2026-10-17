import MicroCFTA.SourceCurrentLeafNumeric
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.SourceCurrentAllocatedNativeInventoryCold
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.EndpointMemoGateSource

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.UncappedForceLeafIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => SourceCurrentConstrainedCapCheckedJointClosed.Plain
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def annotation : Guard := ⟨some [[[0], [1]]], .top⟩
private def expression : Syntax Symbol Guard :=
  .binder false (.node [.mk ("pair", .top) annotation [.var 0, .var 0]])
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def value : Value Symbol Guard := match built with | .done result _ => result | .pending .. => .empty
private def heap := built.state
private def allocated := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def field : SourceEqualityConstraintAllocation.Value := match allocated.1 with
  | .ok value => value
  | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial allocated.2
private def machine : Machine Symbol Guard := ⟨heap, Cache.emptyState⟩
private def before (width : Nat) : Checked width := ⟨initial width machine, operations⟩

private theorem cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem allocation : allocated = (.ok field, allocated.2) := by cbv
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState allocated.2 [annotation] := by
  simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
    (.start Cache.emptyState) cached allocation
private theorem constructed : built = .done value heap := by
  obtain ⟨result, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, value, heap, done, InternedNestedConstruction.Outcome.state]
private theorem initial (width : Nat) : SourceCurrentConjunctionClassScan.Ready (before width) ∧
    Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  apply SourceCurrentConjunctionClassHistoryEntry.constructed width history Cache.empty_valid expression
    (fun original member => by simpa only [expression, SourceEqualityConstraintOrigins.guards,
      SourceEqualityConstraintOrigins.edgeGuards, SourceEqualityConstraintOrigins.childGuards,
      List.nil_append, List.append_nil] using member) value heap constructed
private theorem guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap := by
  simpa only [heap, built] using SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
private def inventory : SourceCurrentAllocatedNativeInventoryState.Inventory :=
  SourceCurrentAllocatedNativeInventoryCold.pairInventory heap (initial 0).1.good.native.machine.1 value value
    (initial 0).2.2.2 (initial 0).2.2.2 (initial 0).2.1 (initial 0).2.1 (initial 0).2.2.1 (initial 0).2.2.1
private def profile : SourceCurrentAllocatedNativeResourceForecast.Profile :=
  ⟨heap.nodes.next, heap.edges.next, machine.domains.next, InternedValueMassHeap.initialBound heap⟩
private theorem initial_fits (width : Nat) : Fits profile (before width) :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap (initial width).1.good.native.machine.1⟩

private theorem no_cap (depth : Nat) : ¬Cap depth value := by
  intro bounded
  cbv at bounded
  cases bounded with
  | plain _ annotated =>
      cases annotated with
      | mu _ _ _ _ body =>
          cases body with
          | node _ _ _ _ annotations _ =>
              have rejected := annotations _ List.mem_cons_self
              change SourceMemoGate.plain annotation = true at rejected
              have invalid : SourceMemoGate.plain annotation = false := by cbv
              rw [invalid] at rejected
              cases rejected

local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "Operands" => SourceEqualityClassTarget.operandPaths
namespace Forecast
export SourceCurrentConstrainedCapSharedForecast (forceProfile ForceReserved forceFuel leafProfile LeafReserved leafFuel)
end Forecast
namespace Worker
export SourceCurrentAllocatedSharedTargetWorker (force leaf Outcome)
end Worker
private def inputs : List (Value Symbol Guard) := [value, value, .reference .depth]
private theorem input_available : InternedNestedProvenance.Values heap inputs := by
  intro original member
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (initial 0).2.1
  · exact (initial 0).2.1
  · exact InternedNestedProvenance.depth_available _
private theorem open_input : ¬MergedColdReaderClosedInputs.ClosedValues inputs := by
  intro closed
  have impossible := closed (.reference .depth) (by simp [inputs])
  cases impossible
private theorem first_domain : Domain [0] inputs := by
  simpa [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionPathDomain.NodeClosed,
    SourceEqualityProjectionGraph.select, inputs] using (initial 0).2.2.1
private theorem second_domain : Domain [1] inputs := by
  simpa [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionPathDomain.NodeClosed,
    SourceEqualityProjectionGraph.select, inputs] using (initial 0).2.2.1
private theorem empty_covered (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient
      (SourceCurrentMemoMergeGraph.empty : SourceCurrentMemoMergeGraph.Memo Symbol Guard) := by
  intro ambient key entry absent
  cases absent
private theorem power_large (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.add_assoc, Nat.pow_succ]
      omega

private theorem exists_room (p : SourceCurrentAllocatedNativeResourceForecast.Profile) :
    ∃ bits, SourceCurrentAllocatedNativeResourceForecast.Room bits p := by
  let total := p.nodes + p.edges + p.domains + 2 ^ (p.nodes + p.nodes * p.nodes)
  refine ⟨total + 1, ?_⟩
  have large := power_large total
  have one := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 1 by omega)
  have two := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 2 by omega)
  change p.nodes < 2 ^ (total + 1) ∧ p.edges ≤ 2 ^ (total + 1 + 2) ∧
    p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) < 2 ^ (total + 1 + 1)
  have nodes : p.nodes ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right p.nodes p.edges)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have edges : p.edges ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_left p.edges p.nodes)
      (Nat.le_add_right (p.nodes + p.edges) p.domains))
      (Nat.le_add_right (p.nodes + p.edges + p.domains) _)
  have domains : p.domains + 2 ^ (p.nodes + p.nodes * p.nodes) ≤ total :=
    Nat.add_le_add_right (Nat.le_add_left p.domains (p.nodes + p.edges)) _
  exact ⟨Nat.lt_of_le_of_lt nodes large,
    Nat.le_trans edges (Nat.le_trans (Nat.le_of_lt large) two),
    Nat.lt_of_le_of_lt domains (Nat.lt_of_lt_of_le large one)⟩

private def record : SourceEqualityClassOrder.Record :=
  match SourceEqualityClassOrder.recordOf [[0], [1]] with
  | some value => value
  | none => ⟨.empty, []⟩
private theorem record_built : SourceEqualityClassOrder.recordOf [[0], [1]] = some record := by cbv
private theorem record_paths : record.paths = [[0], [1]] := by cbv
private theorem record_coherent : SourceEqualityClassOrder.Coherent record := by
  obtain ⟨actual, done, coherent, _paths⟩ :=
    SourceEqualityClassOrder.recordOf_complete [[0], [1]]
      ((EqualityTrie.toPathTrie_succeeds_iff _).mp ⟨.branch [(0, .terminal), (1, .terminal)], by cbv⟩)
  have same : actual = record := Option.some.inj (done.symm.trans record_built)
  exact same ▸ coherent
private theorem record_active : EqualityNormalize.Nontrivial record.paths := by
  rw [record_paths]
  exact ⟨[0], by simp, [1], by simp, by decide⟩
private theorem member : [0] ∈ record.paths := by rw [record_paths]; simp
private theorem domains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) inputs := by
  intro path present
  rw [record_paths] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact first_domain
  · exact second_domain
private def start (width : Nat) : Shared width :=
  SourceCurrentAllocatedSharedTargetState.initial (before width) SourceCurrentMemoMergeGraph.empty
private theorem start_ready (width : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (values : List (Value Symbol Guard)) :
    SharedReady formulas solver inventory record values heap (start width) := by
  have frame := Frame.initial formulas solver inventory machine operations (initial width).1 guards rfl
  exact SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values heap
    (before width) SourceCurrentMemoMergeGraph.empty (initial width).1 frame.admitted
    (SourceEqualityRequiredCache.pure_keeps heap (initial width).1.semantic.ready)
    (SourceCurrentMemoMergeEffects.stored_empty _) (empty_covered formulas solver)
private theorem initially_missing (width : Nat) : (start width).targets [0] = none := rfl
private theorem operand_paths : Operands record.paths [0] = [[1]] := by rw [record_paths]; rfl
private def firstForceProfile := Forecast.forceProfile inputs.length [[1]] false profile
private def firstLeafProfile := Forecast.leafProfile inputs.length [[1]] false profile
private def finalLeafProfile := Forecast.leafProfile inputs.length [[1]] true firstLeafProfile
private theorem force_reserved_of_room (bits count : Nat) (paths : List (List Int)) (found : Bool)
    (numeric : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits (Forecast.forceProfile count paths found numeric)) :
    Forecast.ForceReserved bits count paths found numeric := by
  cases found with
  | true => trivial
  | false =>
      cases paths with
      | nil => trivial
      | cons seed rest =>
          exact SourceCurrentConstrainedCapTargetForecast.reserved_of_final_room bits count seed rest numeric room

private theorem leaf_reserved_of_room (bits count : Nat) (paths : List (List Int)) (found : Bool)
    (numeric : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits (Forecast.leafProfile count paths found numeric)) :
    Forecast.LeafReserved bits count paths found numeric := by
  have forceRoom := room.mono
    (SourceCurrentConstrainedCapSharedForecast.forceProfile_le_leafProfile count paths found numeric)
  exact ⟨force_reserved_of_room bits count paths found numeric forceRoom, forceRoom⟩

/-- A closed non-Cap source constructs a miss and its exact full-state zero-fuel warm hit. -/
theorem constructed_force_warm (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
      ∃ target after next final,
        (start (bits + 2)).targets [0] = none ∧
        ForceReceipt formulas solver next record inputs heap [0] (start (bits + 2)) target after
          EndpointMemoGateTrace.empty final ∧
        Frame formulas solver next after.checked ∧ Fits firstForceProfile after.checked ∧
        Worker.force (Forecast.forceFuel inputs.length [[1]] false profile)
          (Forecast.forceFuel inputs.length [[1]] false profile) (Forecast.forceFuel inputs.length [[1]] false profile)
          (Forecast.forceFuel inputs.length [[1]] false profile) (Forecast.forceFuel inputs.length [[1]] false profile)
          record inputs [0] (start (bits + 2)) = .done target after ∧
        SourceCurrentAllocatedSharedTargetForce.Force record inputs [0] after target after ∧
        Worker.force 0 0 0 0 0 record inputs [0] after = .done target after := by
  have reserved : Forecast.ForceReserved bits inputs.length (Operands record.paths [0])
      ((start (bits + 2)).targets [0]).isSome profile := by
    rw [operand_paths, initially_missing]
    trivial
  have frame := Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl
  obtain ⟨target, after, next, final, receipt, returned, fits, done⟩ :=
    SourceCurrentForceNumeric.complete formulas solver inventory record inputs heap (start (bits + 2)) profile
      (start_ready (bits + 2) formulas solver inputs) frame (initial_fits (bits + 2)) input_available domains
      record_coherent record_active [0] member EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) reserved
  have exactFits : Fits firstForceProfile after.checked := by
    simpa only [firstForceProfile, operand_paths, initially_missing, Option.isSome_none] using fits
  have exactDone : Worker.force (Forecast.forceFuel inputs.length [[1]] false profile)
      (Forecast.forceFuel inputs.length [[1]] false profile) (Forecast.forceFuel inputs.length [[1]] false profile)
      (Forecast.forceFuel inputs.length [[1]] false profile) (Forecast.forceFuel inputs.length [[1]] false profile)
      record inputs [0] (start (bits + 2)) = .done target after := by
    simpa only [operand_paths, initially_missing, Option.isSome_none] using done
  exact ⟨no_cap, open_input, target, after, next, final, initially_missing _, receipt, returned, exactFits,
    exactDone, .hit receipt.present, SourceCurrentAllocatedSharedTargetWorker.force_hit 0 0 0 0 0 record inputs [0] after target receipt.present⟩

/-- Two own Leaf returns retain a produced warm slot and feed the first result into the second query. -/
theorem constructed_leaf_result_fed (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    (∀ depth, ¬Cap depth value) ∧ ¬MergedColdReaderClosedInputs.ClosedValues inputs ∧
      ∃ bits first middle firstInventory firstGlobals result after next final target,
        (start (bits + 2)).targets [0] = none ∧
        LeafReceipt formulas solver firstInventory record inputs heap [0] value (start (bits + 2)) first middle
          EndpointMemoGateTrace.empty firstGlobals ∧
        Frame formulas solver firstInventory middle.checked ∧ Fits firstLeafProfile middle.checked ∧
        Worker.leaf (Forecast.leafFuel inputs.length [[1]] false profile)
          (Forecast.leafFuel inputs.length [[1]] false profile) (Forecast.leafFuel inputs.length [[1]] false profile)
          (Forecast.leafFuel inputs.length [[1]] false profile) (Forecast.leafFuel inputs.length [[1]] false profile)
          record inputs [0] value (start (bits + 2)) = .done first middle ∧
        middle.targets [0] = some target ∧
        Worker.force 0 0 0 0 0 record inputs [0] middle = .done target middle ∧
        LeafReceipt formulas solver next record inputs heap [0] first middle result after firstGlobals final ∧
        Frame formulas solver next after.checked ∧ Fits finalLeafProfile after.checked ∧
        after.targets [0] = some target ∧
        Worker.leaf (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile)
          (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile) (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile)
          (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile) (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile)
          record inputs [0] first middle = .done result after := by
  obtain ⟨bits, room⟩ := exists_room finalLeafProfile
  have firstRoom := room.mono (SourceCurrentConstrainedCapSharedForecast.leafProfile_ge inputs.length [[1]] true firstLeafProfile)
  have firstReserved : Forecast.LeafReserved bits inputs.length (Operands record.paths [0])
      ((start (bits + 2)).targets [0]).isSome profile := by
    simpa only [operand_paths, initially_missing, Option.isSome_none] using
      leaf_reserved_of_room bits inputs.length [[1]] false profile firstRoom
  have frame := Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl
  obtain ⟨first, middle, firstInventory, firstGlobals, firstReceipt, firstFrame, firstFits, firstDone⟩ :=
    SourceCurrentLeafNumeric.complete formulas solver inventory record inputs heap (start (bits + 2)) profile
      (start_ready (bits + 2) formulas solver inputs) frame (initial_fits (bits + 2)) input_available domains
      record_coherent record_active [0] member value (initial 0).2.1 (initial 0).2.2.1
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) firstReserved
  have exactFirstFits : Fits firstLeafProfile middle.checked := by
    simpa only [firstLeafProfile, operand_paths, initially_missing, Option.isSome_none] using firstFits
  have exactFirstDone : Worker.leaf (Forecast.leafFuel inputs.length [[1]] false profile)
      (Forecast.leafFuel inputs.length [[1]] false profile) (Forecast.leafFuel inputs.length [[1]] false profile)
      (Forecast.leafFuel inputs.length [[1]] false profile) (Forecast.leafFuel inputs.length [[1]] false profile)
      record inputs [0] value (start (bits + 2)) = .done first middle := by
    simpa only [operand_paths, initially_missing, Option.isSome_none] using firstDone
  obtain ⟨target, present⟩ : ∃ target, middle.targets [0] = some target := by
    cases firstReceipt.reads with
    | apply forced query => exact ⟨_, forced.present⟩
  have secondReserved : Forecast.LeafReserved bits inputs.length (Operands record.paths [0])
      (middle.targets [0]).isSome firstLeafProfile := by
    simpa only [operand_paths, present, Option.isSome_some] using
      leaf_reserved_of_room bits inputs.length [[1]] true firstLeafProfile room
  obtain ⟨result, after, next, final, receipt, returned, fits, done⟩ :=
    SourceCurrentLeafNumeric.complete formulas solver firstInventory record inputs heap middle firstLeafProfile
      firstReceipt.ready firstFrame exactFirstFits input_available domains record_coherent record_active [0] member
      first firstReceipt.available firstReceipt.closed firstGlobals firstReceipt.globals.valid secondReserved
  have exactFits : Fits finalLeafProfile after.checked := by
    simpa only [finalLeafProfile, operand_paths, present, Option.isSome_some] using fits
  have exactDone : Worker.leaf (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile)
      (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile) (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile)
      (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile) (Forecast.leafFuel inputs.length [[1]] true firstLeafProfile)
      record inputs [0] first middle = .done result after := by
    simpa only [operand_paths, present, Option.isSome_some] using done
  exact ⟨no_cap, open_input, bits, first, middle, firstInventory, firstGlobals, result, after, next, final, target,
    initially_missing _, firstReceipt, firstFrame, exactFirstFits, exactFirstDone, present,
    SourceCurrentAllocatedSharedTargetWorker.force_hit 0 0 0 0 0 record inputs [0] middle target present,
    receipt, returned, exactFits, receipt.slots _ _ present, exactDone⟩

private noncomputable def empty_after (width : Nat) : Shared width :=
  (Worker.force 1 0 2 0 0 record [] [0] (start width)).state
private theorem empty_done (width : Nat) : Worker.force 1 0 2 0 0 record [] [0] (start width) =
    .done .empty (empty_after width) := by cbv

/-- Missing original endpoints construct their empty-forest target and exact warm reuse without query room. -/
theorem constructed_empty_force (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ after next final,
      ForceReceipt formulas solver next record [] heap [0] (start (bits + 2)) .empty after EndpointMemoGateTrace.empty final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.forceProfile 0 [[1]] false profile) after.checked ∧
      Worker.force (Forecast.forceFuel 0 [[1]] false profile) (Forecast.forceFuel 0 [[1]] false profile)
        (Forecast.forceFuel 0 [[1]] false profile) (Forecast.forceFuel 0 [[1]] false profile)
        (Forecast.forceFuel 0 [[1]] false profile) record [] [0] (start (bits + 2)) = .done .empty after ∧
      Worker.force 0 0 0 0 0 record [] [0] after = .done .empty after := by
  have frame := Frame.initial formulas solver inventory machine operations (initial (bits + 2)).1 guards rfl
  have known : InternedNestedProvenance.Values heap [] := by intro value member; cases member
  have selected : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) ([] : List (Value Symbol Guard)) := by
    intro path included
    rw [record_paths] at included
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl <;> simp [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionGraph.select]
  have reserved : Forecast.ForceReserved bits 0 (Operands record.paths [0])
      ((start (bits + 2)).targets [0]).isSome profile := by
    rw [operand_paths, initially_missing]
    trivial
  obtain ⟨result, after, next, final, receipt, returned, fits, done⟩ :=
    SourceCurrentForceNumeric.complete formulas solver inventory record [] heap (start (bits + 2)) profile
      (start_ready (bits + 2) formulas solver []) frame (initial_fits (bits + 2)) known selected record_coherent record_active
      [0] member EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap) reserved
  let budget := Forecast.forceFuel 0 [[1]] false profile
  have exactDone : Worker.force budget budget budget budget budget record [] [0] (start (bits + 2)) = .done result after := by
    simpa only [operand_paths, initially_missing, Option.isSome_none, List.length_nil] using done
  have own := empty_done (bits + 2)
  have first := SourceCurrentAllocatedSharedTargetWorkerStability.force_done_stable own
    (Nat.le_max_left 1 budget) (Nat.le_max_left 0 budget) (Nat.le_max_left 2 budget)
    (Nat.le_max_left 0 budget) (Nat.le_max_left 0 budget)
  have second := SourceCurrentAllocatedSharedTargetWorkerStability.force_done_stable exactDone
    (Nat.le_max_right 1 budget) (Nat.le_max_right 0 budget) (Nat.le_max_right 2 budget)
    (Nat.le_max_right 0 budget) (Nat.le_max_right 0 budget)
  have same := Worker.Outcome.done.inj (first.symm.trans second)
  have resultEmpty := same.1
  subst result
  refine ⟨after, next, final, receipt, returned, ?_, ?_,
    SourceCurrentAllocatedSharedTargetWorker.force_hit 0 0 0 0 0 record [] [0] after .empty receipt.present⟩
  · simpa only [operand_paths, initially_missing, Option.isSome_none, List.length_nil] using fits
  · simpa only [operand_paths, initially_missing, Option.isSome_none, List.length_nil] using done

end MicroCFTA.UncappedForceLeafIntegration

#check @MicroCFTA.UncappedForceLeafIntegration.constructed_force_warm
#print axioms MicroCFTA.UncappedForceLeafIntegration.constructed_force_warm

#check @MicroCFTA.UncappedForceLeafIntegration.constructed_leaf_result_fed
#print axioms MicroCFTA.UncappedForceLeafIntegration.constructed_leaf_result_fed

#check @MicroCFTA.UncappedForceLeafIntegration.constructed_empty_force
#print axioms MicroCFTA.UncappedForceLeafIntegration.constructed_empty_force
