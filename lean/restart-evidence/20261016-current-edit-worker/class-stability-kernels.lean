import MicroCFTA.SourceCurrentAllocatedClassWorkerStability

namespace MicroCFTA.CurrentClassWorkerStabilityIntegration
open InternedConstructorTemplates SourceCurrentAllocatedClassWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

theorem empty_pass_preserves_caches_while_propagating_at_every_bound
    (e p h m s n : Nat) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) :
    pass e p h m s n [] values before memo =
      .done (EqualityLeafProjectionRuntimeEmpty.propagate values) before memo :=
  SourceCurrentAllocatedClassWorkerStability.pass_done_stable
    (pass_nil 0 0 0 0 0 0 values before memo)
    (Nat.zero_le e) (Nat.zero_le p) (Nat.zero_le h) (Nat.zero_le m) (Nat.zero_le s) (Nat.zero_le n)

theorem failed_right_tail_does_not_start_the_head_class
    (e p h m s n : Nat) (record : Record) (records : List Record)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (fault : SourceCurrentAllocatedSharedEditWorker.Fault width) (after : Shared width)
    (failed : fold e p h m s n records values before memo = .failed fault after) :
    fold e p h m s n (record :: records) values before memo = .failed fault after := by
  simp only [fold, failed, Outcome.bind]

theorem successful_noncomparable_bounds_retain_full_checked_state
    (e p h m s n E P H M S N : Nat) (records : List Record)
    (values first second : List (Value Symbol Guard)) (before after later : Checked width) (memo saved current : Memo)
    (one : pass e p h m s n records values before memo = .done first after saved)
    (two : pass E P H M S N records values before memo = .done second later current) :
    first = second ∧ after = later ∧
      after.native.nodes = later.native.nodes ∧ after.native.edges = later.native.edges ∧
      after.native.machine.domains = later.native.machine.domains ∧
      after.operations = later.operations ∧ saved = current := by
  obtain ⟨valuesEqual, checkedEqual, memosEqual⟩ :=
    SourceCurrentAllocatedClassWorkerStability.pass_done_unique one two
  exact ⟨valuesEqual, checkedEqual, congrArg (fun state => state.native.nodes) checkedEqual,
    congrArg (fun state => state.native.edges) checkedEqual,
    congrArg (fun state => state.native.machine.domains) checkedEqual,
    congrArg SourceEqualityNativeDemand.State.operations checkedEqual, memosEqual⟩

theorem one_class_success_survives_independent_bound_increases
    (e p h m s n extraE extraP extraH extraM extraS extraN : Nat)
    (record : Record) (values results : List (Value Symbol Guard))
    (before after : Checked width) (memo saved : Memo)
    (done : runClass e p h m s n record values before memo = .done results after saved) :
    runClass (e + extraE) (p + extraP) (h + extraH) (m + extraM) (s + extraS) (n + extraN)
      record values before memo = .done results after saved :=
  SourceCurrentAllocatedClassWorkerStability.runClass_done_stable done
    (Nat.le_add_right _ _) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    (Nat.le_add_right _ _) (Nat.le_add_right _ _) (Nat.le_add_right _ _)

end MicroCFTA.CurrentClassWorkerStabilityIntegration
