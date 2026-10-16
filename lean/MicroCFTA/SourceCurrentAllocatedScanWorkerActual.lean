import MicroCFTA.SourceCurrentAllocatedScanWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedScanWorkerStability
import MicroCFTA.SourceCurrentAllocatedScanCaller

/-!
# Full caller receipts for literal current Scan execution

Initial physical facts and reached ranges construct a current Scan graph.
Literal success uniqueness identifies its complete result and returned state
with any supplied success. Strict source reads and full caller receipts then
apply to that same return. No future graph or final invariant is an input
of finite literal execution. Concrete host table execution remains separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedScanWorkerActual
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionClassScan (Scan Ready)
open SourceCurrentAllocatedScanSourceReads (ScanReads)
open SourceCurrentAllocatedScanWorker (scan)
open SourceCurrentAllocatedScanWorkerCompletion (StableRun)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Legitimate initial physical facts align supplied success with the same actual Scan graph. -/
theorem sound {g s p h n budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {outcome : Option Class} {before after : Checked width} {memo saved : Memo}
    (done : scan g s p h n budget values classes before memo = .done (outcome, selected) after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget unconstrained reaches values classes before memo) :
    Scan budget unconstrained reaches values classes before memo outcome selected after saved := by
  obtain ⟨chosen, kept, reached, current, actual, _⟩ := SourceCurrentConjunctionClassScanCompletion.finite
    formulas solver budget unconstrained reaches values classes before memo ready available proper correct ranges
  obtain ⟨G, S, P, H, N, stable⟩ := SourceCurrentAllocatedScanWorkerCompletion.scan_complete actual
  obtain ⟨same, rfl, rfl⟩ := SourceCurrentAllocatedScanWorkerStability.scan_done_unique
    (stable G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact actual

/-- A supplied literal return derives its own strict reads, full caller, and stopped-class law. -/
theorem verified {inventory : Inventory} {g s p h n budget : Nat}
    {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before : Caller width} {after : Checked width} {saved : Memo} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (ranges : Ranges budget unconstrained reaches values classes before.checked before.fourth)
    (done : scan g s p h n budget values classes before.checked before.fourth = .done (outcome, selected) after saved) :
    ∃ next final,
      ∃ actual : Scan budget unconstrained reaches values classes before.checked before.fourth outcome selected after saved,
        ScanReads actual memos final ∧ Post formulas solver next before
          (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
        Values after.native.machine.heap values ∧ selected.Sublist classes ∧
        SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values classes outcome := by
  have actual := sound formulas solver done initial.ready available proper initial.correct ranges
  obtain ⟨next, final, reads, post⟩ := SourceCurrentAllocatedScanCaller.actual formulas solver actual initial
    available proper active ranges
  exact ⟨next, final, actual, reads, post⟩

/-- Initial caller facts construct stable literal Scan and its same complete returned invariant. -/
theorem finite {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (values : List (Value Symbol Guard)) (classes : Constraints)
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (ranges : Ranges budget unconstrained reaches values classes before.checked before.fourth) :
    ∃ outcome selected after saved next final,
      StableRun (fun g s p h n => scan g s p h n budget values classes before.checked before.fourth)
        (outcome, selected) after saved ∧
      ∃ actual : Scan budget unconstrained reaches values classes before.checked before.fourth outcome selected after saved,
        ScanReads actual memos final ∧ Post formulas solver next before
          (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
        Values after.native.machine.heap values ∧ selected.Sublist classes ∧
        SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values classes outcome := by
  obtain ⟨outcome, selected, after, saved, next, final, actual, reads, post⟩ :=
    SourceCurrentAllocatedScanCaller.finite formulas solver budget values classes initial available proper active ranges
  exact ⟨outcome, selected, after, saved, next, final,
    SourceCurrentAllocatedScanWorkerCompletion.scan_complete actual, actual, reads, post⟩

end MicroCFTA.SourceCurrentAllocatedScanWorkerActual
