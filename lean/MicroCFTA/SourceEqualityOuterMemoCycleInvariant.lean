import MicroCFTA.SourceEqualityOuterMemoWorkerCycle
import MicroCFTA.SourceEqualityPartialMemoFrame

/-!
# Complete table validity of the actual recursive busy cycle

The general recursive frame theorem applies to the exact fixture receipt.
Allocation bounds exclude any other cell. Neither pending request appears
in the completed-result projection, for any physical request key.
-/
namespace MicroCFTA.SourceEqualityOuterMemoCycleInvariant
open SourceObservations SourceSymbolicIndex InternedConstructorTemplates
open SourceEqualityPartialMemoWorker SourceEqualityPartialMemoFrame SourceEqualityOuterMemoWorkerCycle
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- The exact busy observation retains both valid tables and every physical request link. -/
theorem observed_valid (observed : Trace) (found : observation = some observed) : Valid (stateTables observed.state) := by
  have receipts := observation_receipts observed found
  have frame := run_frame 4 4 2 2 2 1024 2 (some []) observed.root
    (initial (SourceEqualityNativeInitial.cold 32 observed.heap)) (initial_valid _)
  rw [receipts.2] at frame
  exact frame.valid

/-- The actual cycle has only its two running cells and no completed result under any key. -/
theorem actual_unfinished : ∃ observed root wrapper,
    observation = some observed ∧ Valid (stateTables observed.state) ∧
    observed.state.memo.cells 0 = some ⟨root, .evaluating⟩ ∧
    observed.state.memo.cells 1 = some ⟨wrapper, .evaluating⟩ ∧
    (∀ handle, 2 ≤ handle → observed.state.memo.cells handle = none) ∧
    (∀ key, FlatMemoThunk.completed observed.state.memo key = none) := by
  obtain ⟨observed, root, wrapper, found, first, second, rest⟩ := actual_pending
  have valid := observed_valid observed found
  have count := rest.2.2.1
  have absent : ∀ handle, 2 ≤ handle → observed.state.memo.cells handle = none := by
    intro handle later
    cases stored : observed.state.memo.cells handle with
    | none => rfl
    | some cell =>
        have bound := valid.2.bounded handle cell stored
        change handle < observed.state.memo.next at bound
        rw [count] at bound
        omega
  refine ⟨observed, root, wrapper, found, valid, first, second, absent, ?_⟩
  intro key
  cases published : observed.state.memo.table key with
  | none => simp [FlatMemoThunk.completed, published]
  | some handle =>
      obtain ⟨cell, stored, linked⟩ := valid.2.linked key handle published
      have bound := valid.2.bounded handle cell stored
      change handle < observed.state.memo.next at bound
      rw [count] at bound
      have cases : handle = 0 ∨ handle = 1 := by omega
      rcases cases with rfl | rfl
      · simp [FlatMemoThunk.completed, published, first]
      · simp [FlatMemoThunk.completed, published, second]

end MicroCFTA.SourceEqualityOuterMemoCycleInvariant
