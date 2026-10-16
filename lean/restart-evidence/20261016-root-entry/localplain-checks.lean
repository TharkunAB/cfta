import MicroCFTA.SourceCurrentAllocatedLocalPlain
import MicroCFTA.SourceCurrentAllocatedPartialActiveOrder

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#check @MicroCFTA.SourceCurrentAllocatedLocalPlain.OwnEmpty
#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlain.of_readback
#check @MicroCFTA.SourceCurrentAllocatedLocalPlain.of_readback
#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlain.of_load
#check @MicroCFTA.SourceCurrentAllocatedLocalPlain.of_load
#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlain.prefix_cases
#check @MicroCFTA.SourceCurrentAllocatedLocalPlain.prefix_cases
#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlain.empty_stages
#check @MicroCFTA.SourceCurrentAllocatedLocalPlain.empty_stages
#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlain.complete
#check @MicroCFTA.SourceCurrentAllocatedLocalPlain.complete
#print axioms MicroCFTA.SourceCurrentAllocatedLocalPlain.done_shape
#check @MicroCFTA.SourceCurrentAllocatedLocalPlain.done_shape

namespace LocalPlainChecks
open MicroCFTA
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedLocalPlain
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

theorem resident_zero_bounds (budget : Nat) (edge : EdgeValue Symbol Guard) (inherited : EqValue)
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (resident : InternedEdgeResidency.EdgeResident before.native.machine.heap edge)
    (inheritedReady : EqReady before.operations.constraints inherited)
    (plain : SourceCompactGuards.sourceEqualities edge.entry.key.constraint = some []) :
    ∃ loaded results,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.operations.constraints = .ok (some loaded) ∧
      SourceCurrentAllocatedLocalWorker.reduce 0 0 0 0 0 0 0 0 0 budget loaded inherited edge.children before fourth memo =
        .done results (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo ∧
      (results = edge.children ∨ results = EqualityLeafProjectionRuntimeEmpty.erase edge.children) := by
  obtain ⟨loaded, found, storedReady, readback, _⟩ :=
    (ready.good.fields edge.entry.key edge resident).receipts ready.good.operations
  obtain ⟨results, done, shape⟩ := complete 0 0 0 0 0 0 0 0 0 budget loaded inherited edge.children before fourth memo
    ready.good.operations storedReady inheritedReady (of_readback readback plain)
  exact ⟨loaded, results, found, done, shape⟩

theorem no_native_work (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values results : List (Value Symbol Guard)) (before after : Checked width)
    (fourth savedFourth : Fourth) (memo saved : Memo)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (storedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (plain : OwnEmpty loaded)
    (done : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo =
      .done results after savedFourth saved) :
    after.native = before.native ∧
      after.operations = (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).2 ∧
      savedFourth = fourth ∧ saved = memo := by
  obtain ⟨rfl, rfl, rfl, _⟩ := done_shape g s r e p h m c n budget loaded inherited values before after
    fourth savedFourth memo saved results valid storedReady inheritedReady plain done
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem returned_edge_bound (g s r e p h m c n budget : Nat)
    (original result : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before after : Checked width) (fourth savedFourth : Fourth) (memo saved : Memo)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (storedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (plain : OwnEmpty loaded)
    (done : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited original.children
      before fourth memo = .done result.children after savedFourth saved) :
    MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight original := by
  have shape := (done_shape g s r e p h m c n budget loaded inherited original.children before after
    fourth savedFourth memo saved result.children valid storedReady inheritedReady plain done).2.2.2
  exact SourceCurrentAllocatedPartialActiveOrder.original_or_erased_bound original result shape

theorem no_failed_observation (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (storedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (plain : OwnEmpty loaded) :
    ¬∃ fault after savedFourth saved,
      SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo =
        .failed fault after savedFourth saved := by
  obtain ⟨results, done, _⟩ := complete g s r e p h m c n budget loaded inherited values before fourth memo
    valid storedReady inheritedReady plain
  rintro ⟨fault, after, savedFourth, saved, failed⟩
  cases done.symm.trans failed

theorem unresolved_forest_needs_no_bound (budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (reference : InternedBinderProtocol.Reference) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (storedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (plain : OwnEmpty loaded) :
    ∃ results,
      SourceCurrentAllocatedLocalWorker.reduce 0 0 0 0 0 0 0 0 0 budget loaded inherited [.reference reference] before fourth memo =
        .done results (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo ∧
      (results = [.reference reference] ∨ results = [.empty]) := by
  exact complete 0 0 0 0 0 0 0 0 0 budget loaded inherited [.reference reference] before fourth memo
    valid storedReady inheritedReady plain

theorem actual_empty_stages_zero (budget : Nat) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo) :
    SourceCurrentAllocatedLocalWorker.classes 0 0 0 0 0 0 0 0 0 budget [] values before fourth memo =
      .done (EqualityLeafProjectionRuntimeEmpty.propagate values) before fourth memo :=
  empty_stages 0 0 0 0 0 0 0 0 0 budget values before fourth memo

end LocalPlainChecks

#print axioms LocalPlainChecks.resident_zero_bounds
#check @LocalPlainChecks.resident_zero_bounds
#print axioms LocalPlainChecks.no_native_work
#check @LocalPlainChecks.no_native_work
#print axioms LocalPlainChecks.returned_edge_bound
#check @LocalPlainChecks.returned_edge_bound
#print axioms LocalPlainChecks.no_failed_observation
#check @LocalPlainChecks.no_failed_observation
#print axioms LocalPlainChecks.unresolved_forest_needs_no_bound
#check @LocalPlainChecks.unresolved_forest_needs_no_bound
#print axioms LocalPlainChecks.actual_empty_stages_zero
#check @LocalPlainChecks.actual_empty_stages_zero
