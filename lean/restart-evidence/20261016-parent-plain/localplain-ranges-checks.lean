import MicroCFTA.SourceCurrentAllocatedLocalPlainRanges
import MicroCFTA.SourceCurrentAllocatedLocalWorkerActual

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlainRanges.nil_ranges
#check @MicroCFTA.SourceCurrentAllocatedLocalPlainRanges.nil_ranges
#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlainRanges.ranges
#check @MicroCFTA.SourceCurrentAllocatedLocalPlainRanges.ranges
#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlainRanges.loaded_ranges
#check @MicroCFTA.SourceCurrentAllocatedLocalPlainRanges.loaded_ranges
#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlainRanges.resident_ranges
#check @MicroCFTA.SourceCurrentAllocatedLocalPlainRanges.resident_ranges

namespace LocalPlainRangesChecks
open MicroCFTA
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedLocalPlainRanges
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {width : Nat}

theorem local_full_post_without_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (initial : Context formulas solver inventory before memos)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (plain : SourceCompactGuards.sourceEqualities original = some []) :
    ∃ results after fourth memo next final,
      SourceCurrentAllocatedLocalWorkerCompletion.StableRun (fun g s r e p h m c n =>
        SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values
          before.checked before.fourth before.merge) results after fourth memo ∧
      Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after fourth memo) final ∧
      (results = values ∨ results = EqualityLeafProjectionRuntimeEmpty.erase values) := by
  have rangePlan := loaded_ranges budget original loaded inherited values before.checked before.fourth before.merge
    initial.ready.good.operations cached found inheritedReady plain
  obtain ⟨results, after, fourth, memo, next, final, stable, _, _, _, post⟩ :=
    SourceCurrentAllocatedLocalWorkerActual.finite formulas solver budget original loaded inherited values
      initial cached found inheritedReady available rangePlan
  have retained := stable
  obtain ⟨g, s, r, e, p, h, m, c, n, done⟩ := stable
  have actual := done g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨ownEmpty, storedReady⟩ := SourceCurrentAllocatedLocalPlain.of_load original before.checked.operations
    initial.ready.good.operations cached loaded found plain
  have shape := (SourceCurrentAllocatedLocalPlain.done_shape g s r e p h m c n budget loaded inherited values
    before.checked after before.fourth fourth before.merge memo results initial.ready.good.operations
    storedReady inheritedReady ownEmpty actual).2.2.2
  exact ⟨results, after, fourth, memo, next, final, retained, post, shape⟩

theorem resident_actual_body_without_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : SourceCurrentAllocatedPartialState.EdgeRequest)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (plain : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
      SourceCompactGuards.sourceEqualities request.value.entry.key.constraint = some []) :
    ∃ result after fourth memo next final,
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
          (SourceCurrentAllocatedPartialState.advance before after fourth memo),
        SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after fourth memo) final ∧
        InternedEdgeResidency.EdgeResident after.native.machine.heap result ∧
        SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result := by
  obtain ⟨result, after, fourth, memo, next, final, _, actual, reads, receipt, post⟩ :=
    SourceCurrentAllocatedParentWorkerActual.resident_finite formulas solver budget request initial inheritedReady
      resident (resident_ranges budget request before initial.ready resident inheritedReady plain)
  exact ⟨result, after, fourth, memo, next, final, actual, reads, post, receipt.resident, receipt.language⟩

theorem full_nil_continuation (budget : Nat) (values : List (Value Symbol Guard))
    (before middle : Checked width) (fourth savedFourth : Fourth) (memo : Memo)
    (selected : Constraints)
    (actual : SourceCurrentConjunctionClassScan.Scan budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values [] before fourth none selected middle savedFourth)
    (kept : List SourceEqualityClassOrder.Record)
    (retained : SourceCurrentConjunctionSelectedRecords.Retained actual [] kept)
    (fuel readFuel : Nat) (requiredValues : List (Value Symbol Guard)) (heap : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
      values middle.native.machine.heap = .done requiredValues heap) :
    SourceCurrentAllocatedClassPass.Ranges kept requiredValues (SourceCurrentConjunctionClassScan.advanceHeap middle heap) memo :=
  (nil_ranges budget values before fourth memo).pass actual kept retained fuel readFuel requiredValues heap done

theorem contradictory_inherited_full_ranges (budget : Nat) (loaded : Allocated)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (storedReady : EqReady before.operations.constraints loaded.stored)
    (plain : SourceCurrentAllocatedLocalPlain.OwnEmpty loaded) :
    SourceCurrentAllocatedLocalReduction.Ranges budget loaded .contradiction values before fourth memo := by
  have inheritedReady : EqReady before.operations.constraints .contradiction := ⟨trivial, by
    simp [SourceEqualityDescend.WellFormed, SourceEqualityConstraintAllocation.Value.payload]⟩
  exact ranges budget loaded .contradiction values before fourth memo valid storedReady inheritedReady plain

end LocalPlainRangesChecks

#print axioms LocalPlainRangesChecks.local_full_post_without_ranges
#check @LocalPlainRangesChecks.local_full_post_without_ranges
#print axioms LocalPlainRangesChecks.resident_actual_body_without_ranges
#check @LocalPlainRangesChecks.resident_actual_body_without_ranges
#print axioms LocalPlainRangesChecks.full_nil_continuation
#check @LocalPlainRangesChecks.full_nil_continuation
#print axioms LocalPlainRangesChecks.contradictory_inherited_full_ranges
#check @LocalPlainRangesChecks.contradictory_inherited_full_ranges
