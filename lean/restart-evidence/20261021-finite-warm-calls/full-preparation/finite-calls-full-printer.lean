import MicroCFTA.SourceCurrentFiniteRoundForecast
import MicroCFTA.SourceCurrentOuterRankAdequacy
import MicroCFTA.SourceCurrentWarmNextPacket

namespace MicroCFTA.SourceCurrentFiniteWarmCalls
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "stage" => SourceCurrentFiniteRoundForecast.stage
local notation "fuelBounds" => SourceCurrentFiniteRoundForecast.fuelBounds
local notation "roomBits" => SourceCurrentParentInitialRoom.roomBits
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-!
# Finite calls through one populated caller

Choose the width and common fuels before the first call.
Keep the inherited value and each actual returned caller.
This result does not include withoutRedundantEdges or assert convergence.
-/
open SourceCurrentAllocatedNativeResourceForecast (Le Room)
local notation "Seed" => List Guard × Profile

private def Entry (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {bits : Nat}
    (seed : Seed) (inherited : EqValue) (current : Node × Caller (bits + 2)) : Prop :=
  ∃ (inventory : Inventory) (memos : Memos),
    Context formulas solver inventory current.2 memos ∧
    Frame formulas solver inventory current.2.checked ∧ Fits seed.2 current.2.checked ∧
    Carrier (fun guard => guard ∈ seed.1) current.2.checked.native.machine.heap ∧
    SourceCurrentOuterPrefixInvariants.NodeReady current.2 ⟨inherited, current.1⟩ ∧
    SourceCurrentRequiredUnionNormal.UnionNormal current.2.checked.native.machine.heap ∧
    SourceCurrentNativeRequestPositivePositions.Support
      current.2.checked.native.machine.heap current.2.checked.native ∧
    Nonempty (SourceCurrentNativeMuPublication.History empty current.2.checked.native.machine.heap) ∧
    SourceCurrentConstrainedCapMemoMerge.Stored
      (fun guard : Guard => SourceMemoGate.plain guard = true) current.2.merge ∧
    SourceCurrentMergePositivePosition.Support current.2.merge ∧
    SourceCurrentResourceParentWriters.Origins formulas solver current.2 ∧
    SourceCurrentOuterClosedInputs.NodeStored current.2 ∧ current.1.free = [] ∧
    (∀ chosen owner, current.2.nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩) ∧
    SourceCurrentOuterEdgeIdle.EdgeIdle current.2

private theorem advance_entry
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget rounds : Nat) (seed : Seed) {index : Nat} (included : index < rounds) :
    let bits := roomBits (stage budget seed rounds).2
    let fuels := fuelBounds budget rounds seed
    ∀ {inherited : EqValue} {current : Node × Caller (bits + 2)},
      Entry formulas solver (stage budget seed index) inherited current →
      ∃ next : Node × Caller (bits + 2),
        nodeCall fuels.1
          fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 budget
          ⟨inherited, current.1⟩ current.2 = .done next.1 next.2 ∧
        Entry formulas solver (stage budget seed (index + 1)) inherited next ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver
          ⟨inherited, current.1⟩ next.1 := by
  dsimp only
  intro inherited current packet
  obtain ⟨inventory, memos, initial, frame, fits, known, inputs, normal,
    supported, ⟨causal⟩, merged, positiveMemo, origins, stored, closed, nodeIdle, edgeIdle⟩ := packet
  let entry := stage budget seed index
  let fuels := fuelBounds budget rounds seed
  let count := SourceCurrentPositiveQuotientCount.count (inherited.payload.getD []) current.1
  let mass := InternedValueMass.value current.1
  let output := SourceCurrentOuterRankEnvelope.envelope budget count mass entry
  let scheduled := SourceCurrentOuterInitialSchedule.node output.1 budget entry
  have massBound : mass ≤ entry.2.mass :=
    InternedValueMassHeap.available _ fits.stored current.1 inputs.2
  have countBound : count ≤ entry.2.mass :=
    Nat.le_trans (SourceCurrentPositiveQuotientCount.count_le_mass _ _) massBound
  have bounds := (SourceCurrentFiniteRoundForecast.stage_bounds budget rounds seed).2
    index included count mass countBound massBound
  have room : Room (roomBits (stage budget seed rounds).2)
      (SourceCurrentInitialSelectionForecast.cover [output.2.2.2] scheduled.2) :=
    bounds.2.2.1
  have outerBound : output.1 ≤ fuels.1 := bounds.2.2.2.1
  have lowerBound : SourceCurrentOuterInitialFuel.nodeNeed output.1 budget entry ≤ fuels.2 :=
    bounds.2.2.2.2
  obtain ⟨result, after, stable⟩ :=
    SourceCurrentOuterRankAdequacy.initial_node_call formulas solver
      (g := fuels.2) (s := fuels.2) (r := fuels.2) (e := fuels.2) (p := fuels.2)
      (h := fuels.2) (m := fuels.2) (c := fuels.2) (n := fuels.2) (budget := budget)
      (request := ⟨inherited, current.1⟩) (before := current.2) entry
      initial frame fits known inputs room normal supported causal merged positiveMemo
      origins stored closed nodeIdle edgeIdle
      lowerBound lowerBound lowerBound lowerBound lowerBound
      lowerBound lowerBound lowerBound lowerBound
  have base := stable output.1 (Nat.le_refl _)
  have observed := stable fuels.1 outerBound
  have scheduleRoom : Room (roomBits (stage budget seed rounds).2) scheduled.2 :=
    room.mono (SourceCurrentInitialSelectionForecast.cover_ge _ _)
  obtain ⟨_next, _final, _actual, _reads, _post, _frame, _fits, _known,
      _available, stepLaw⟩ :=
    SourceCurrentOuterInitialActual.node_call formulas solver output.1 entry
      initial frame fits known inputs.1 inputs.2 scheduleRoom base
  obtain ⟨next, final, post, nextFrame, nextFits, nextKnown, nextInputs,
      nextSupported, nextCausal, nextMerged, nextPositive, nextNormal,
      nextOrigins, nextStored, nextClosed, nextNodeIdle, nextEdgeIdle⟩ :=
    SourceCurrentWarmNextPacket.node_call formulas solver entry
      initial frame fits known inputs scheduleRoom normal supported causal merged
      positiveMemo origins stored closed nodeIdle edgeIdle base
  have nextBounds := (SourceCurrentFiniteRoundForecast.stage_bounds budget (index + 1) seed).2
    index (Nat.lt_succ_self _) count mass countBound massBound
  have growth : Le scheduled.2 (stage budget seed (index + 1)).2 :=
    (SourceCurrentInitialSelectionForecast.cover_ge [output.2.2.2] scheduled.2).trans nextBounds.1
  have nextCarrier : Carrier (fun guard => guard ∈ (stage budget seed (index + 1)).1)
      after.checked.native.machine.heap := by
    intro key edge present
    exact nextBounds.2.1 (List.mem_append_right _ (nextKnown key edge present))
  have nextEntry : Entry formulas solver (stage budget seed (index + 1))
      inherited (result, after) :=
    ⟨next, final, post.context, nextFrame, nextFits.mono growth, nextCarrier,
      nextInputs, nextNormal, nextSupported, nextCausal, nextMerged, nextPositive,
      nextOrigins, nextStored, nextClosed, nextNodeIdle, nextEdgeIdle⟩
  exact ⟨(result, after), observed, nextEntry, stepLaw⟩

/-- A finite trace retains its callers, final availability and inherited-conditioned node law. -/
theorem node_calls
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget rounds : Nat) (seed : List Guard × Profile) :
    let bits := roomBits (stage budget seed rounds).2
    let fuels := fuelBounds budget rounds seed
    ∀ {inherited : EqValue} {value : Node} {before : Caller (bits + 2)}
      {inventory : Inventory} {memos : Memos}
      (_initial : Context formulas solver inventory before memos)
      (_frame : Frame formulas solver inventory before.checked)
      (_fits : Fits seed.2 before.checked)
      (_known : Carrier (fun guard => guard ∈ seed.1) before.checked.native.machine.heap)
      (_inputs : SourceCurrentOuterPrefixInvariants.NodeReady before ⟨inherited, value⟩)
      (_normal : SourceCurrentRequiredUnionNormal.UnionNormal before.checked.native.machine.heap)
      (_supported : SourceCurrentNativeRequestPositivePositions.Support
        before.checked.native.machine.heap before.checked.native)
      (_causal : SourceCurrentNativeMuPublication.History empty before.checked.native.machine.heap)
      (_merged : SourceCurrentConstrainedCapMemoMerge.Stored
        (fun guard : Guard => SourceMemoGate.plain guard = true) before.merge)
      (_positiveMemo : SourceCurrentMergePositivePosition.Support before.merge)
      (_origins : SourceCurrentResourceParentWriters.Origins formulas solver before)
      (_stored : SourceCurrentOuterClosedInputs.NodeStored before)
      (_closed : value.free = [])
      (_nodeIdle : ∀ chosen owner, before.nodeResults.cells chosen ≠ some ⟨owner, .evaluating⟩)
      (_edgeIdle : SourceCurrentOuterEdgeIdle.EdgeIdle before),
    ∃ trace : Fin (rounds + 1) → Node × Caller (bits + 2),
      trace 0 = (value, before) ∧
      (∀ index : Fin rounds,
        nodeCall fuels.1
          fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 budget
          ⟨inherited, (trace index.castSucc).1⟩ (trace index.castSucc).2 =
            .done (trace index.succ).1 (trace index.succ).2) ∧
      Available (trace (Fin.last rounds)).2.checked.native.machine.heap (trace (Fin.last rounds)).1 ∧
      SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver
        ⟨inherited, value⟩ (trace (Fin.last rounds)).1
 := by
  dsimp only
  intro inherited value before inventory memos initial frame fits known inputs normal
    supported causal merged positiveMemo origins stored closed nodeIdle edgeIdle
  let fuels := fuelBounds budget rounds seed
  have firstEntry : Entry formulas solver seed inherited (value, before) :=
    ⟨inventory, memos, initial, frame, fits, known, inputs, normal, supported,
      ⟨causal⟩, merged, positiveMemo, origins, stored, closed, nodeIdle, edgeIdle⟩
  have prefixes : ∀ length, length ≤ rounds →
      ∃ trace : Nat → Node × Caller (roomBits (stage budget seed rounds).2 + 2),
        trace 0 = (value, before) ∧
        (∀ index, index < length →
          nodeCall fuels.1
            fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 fuels.2 budget
            ⟨inherited, (trace index).1⟩ (trace index).2 =
              .done (trace (index + 1)).1 (trace (index + 1)).2) ∧
        Entry formulas solver (stage budget seed length) inherited (trace length) ∧
        SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver
          ⟨inherited, value⟩ (trace length).1 := by
    intro length
    induction length with
    | zero =>
        intro _bound
        refine ⟨fun _ => (value, before), rfl, ?_, firstEntry,
          SourceCurrentAllocatedPartialCallSteps.node_refl formulas solver _⟩
        intro index impossible
        omega
    | succ length ih =>
        intro bound
        have included : length < rounds := by omega
        obtain ⟨trace, first, steps, lastEntry, cumulative⟩ := ih (by omega)
        obtain ⟨next, observed, nextEntry, stepLaw⟩ :=
          advance_entry formulas solver budget rounds seed included lastEntry
        have nextLaw : SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver
            ⟨inherited, value⟩ next.1 := by
          intro ambient term
          refine ⟨?_, ?_⟩
          · intro accepted
            exact (cumulative ambient term).1 ((stepLaw ambient term).1 accepted)
          · intro satisfied
            exact ((stepLaw ambient term).2 satisfied).trans
              ((cumulative ambient term).2 satisfied)
        let extended : Nat → Node × Caller (roomBits (stage budget seed rounds).2 + 2) :=
          fun index => if index = length + 1 then next else trace index
        have unchanged (index : Nat) (earlier : index ≤ length) :
            extended index = trace index := by
          have distinct : index ≠ length + 1 := by omega
          exact ite_eq_right distinct
        have latest : extended (length + 1) = next := by
          exact ite_eq_left rfl
        refine ⟨extended, ?_, ?_, ?_, ?_⟩
        · rw [unchanged 0 (Nat.zero_le _)]
          exact first
        · intro index inside
          by_cases atLast : index = length
          · subst index
            rw [unchanged length (Nat.le_refl _), latest]
            exact observed
          · have earlier : index < length := by omega
            rw [unchanged index (by omega), unchanged (index + 1) (by omega)]
            exact steps index earlier
        · rw [latest]
          exact nextEntry
        · rw [latest]
          exact nextLaw
  obtain ⟨trace, first, steps, lastEntry, law⟩ := prefixes rounds (Nat.le_refl _)
  obtain ⟨_inventory, _memos, _initial, _frame, _fits, _known, lastInputs, _rest⟩ := lastEntry
  refine ⟨fun index => trace index.val, first, ?_, lastInputs.2, law⟩
  intro index
  exact steps index.val index.isLt

end MicroCFTA.SourceCurrentFiniteWarmCalls

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentFiniteWarmCalls.node_calls
#print MicroCFTA.SourceCurrentFiniteWarmCalls.node_calls
#print axioms MicroCFTA.SourceCurrentFiniteWarmCalls.node_calls
