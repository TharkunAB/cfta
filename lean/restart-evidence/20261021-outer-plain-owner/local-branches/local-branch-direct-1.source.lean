import MicroCFTA.SourceCurrentAllocatedLocalWorkerStability
import MicroCFTA.SourceEqualityPartialInheritedPlainPass

/-!
# Actual successful local reduction branches

A successful literal reduction retains the original children, erases
their slots, or completes a nonempty selected class pass. The selected
case keeps the same precheck, Scan, Required and pass returns. The
required forest starts from the original children at the Scan return.
No semantic invariant or future caller return is required.
-/
namespace MicroCFTA.SourceCurrentActualLocalBranchCases
open EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedLocalWorker
open SourceCurrentAllocatedLocalWorkerStability
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq Node] {width : Nat}

/-- A literal success supplies its exact original, erased or selected continuation. -/
theorem reduce_cases {g s r e p h m c n budget : Nat} {loaded : Allocated}
    {inherited : EqValue} {values results : List Node} {before after : Checked width}
    {fourth saved : Fourth} {memo current : Memo}
    (actual : reduce g s r e p h m c n budget loaded inherited values before fourth memo =
      .done results after saved current) :
    results = values ∨ results = EqualityLeafProjectionRuntimeEmpty.erase values ∨
      ∃ (records kept : List Record) (scanned : Checked width) (scanFourth : Fourth)
        (prepared : List Node) (preparedHeap : Heap),
        (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 =
          .ok (.classes records) ∧
        SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
          (prefixState before loaded inherited) fourth = .done (none, kept) scanned scanFourth ∧
        kept ≠ [] ∧
        SourceEqualityRequiredExecution.requireAll r h
          (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) values scanned.native.machine.heap =
          .done prepared preparedHeap ∧
        SourceCurrentAllocatedClassWorker.pass e p h m c n kept prepared
          (advanceHeap scanned preparedHeap) memo = .done results after current ∧
        saved = scanFourth := by
  cases checked : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 with
  | error message =>
      simp only [reduce, checked] at actual
      cases actual
  | ok branch =>
      cases branch with
      | unchanged =>
          simp only [reduce, checked] at actual
          cases actual
          exact Or.inl rfl
      | emptyChildren =>
          simp only [reduce, checked] at actual
          cases actual
          exact Or.inr (Or.inl rfl)
      | classes records =>
          have completed : classes g s r e p h m c n budget records values
              (prefixState before loaded inherited) fourth memo = .done results after saved current := by
            simpa only [reduce, checked, SourceCurrentAllocatedPrecheck.state] using actual
          obtain ⟨selection, scanned, scanFourth, scanMemo, first, later⟩ :=
            (bind_done_iff _ _ _ _ _ _).mp completed
          obtain ⟨scanCall, rfl⟩ := scan_done_iff.mp first
          cases selection with
          | mk stopped kept =>
              cases stopped with
              | some paths =>
                  cases later
                  exact Or.inr (Or.inl rfl)
              | none =>
                  by_cases empty : kept = []
                  · subst kept
                    have noPaths : SourceEqualitySelectedRequired.paths ([] : Constraints) = [] := by
                      simp [SourceEqualitySelectedRequired.paths, canonicalClass]
                    simp only [List.map_nil, noPaths, required,
                      SourceEqualityRequiredExecution.requireAll_identity, Outcome.bind,
                      pass, SourceCurrentAllocatedClassWorker.pass_nil] at later
                    cases later
                    rcases SourceEqualityPartialInheritedPlainPass.propagate_shape values with original | erased
                    · exact Or.inl original
                    · exact Or.inr (Or.inl erased)
                  · obtain ⟨prepared, preparedBefore, nextFourth, warm, requiredDone, passDone⟩ :=
                      (bind_done_iff _ _ _ _ _ _).mp later
                    obtain ⟨preparedHeap, requiredCall, rfl, rfl, rfl⟩ := required_done_iff.mp requiredDone
                    obtain ⟨passCall, sameFourth⟩ := pass_done_iff.mp passDone
                    exact Or.inr (Or.inr ⟨records, kept, scanned, scanFourth, prepared, preparedHeap,
                      checked, scanCall, empty, requiredCall, passCall, sameFourth⟩)

end MicroCFTA.SourceCurrentActualLocalBranchCases
