import MicroCFTA.SourceCurrentConjunctionRequired

/-!
# Required-path receipts for an actual current Scan continuation

The actual completed required call has the same result and constructor heap
as the finite call derived from the selected primary certificates. The proof
uses completed graph uniqueness. It retains the actual returned state.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequiredActual
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready Scan advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- Two actual completed required calls agree at arbitrary completed bounds. -/
theorem required_unique
    {fuel readFuel otherFuel otherReadFuel : Nat} {paths : List SourceEqualityNeeded.Path}
    {values first second : List (Value Symbol Guard)}
    {before afterFirst afterSecond : State Symbol Guard}
    (one : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done first afterFirst)
    (two : SourceEqualityRequiredExecution.requireAll otherFuel otherReadFuel paths values before = .done second afterSecond) :
    first = second ∧ afterFirst = afterSecond := by
  have left := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before first afterFirst).mpr
    ⟨fuel, readFuel, one⟩
  have right := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before second afterSecond).mpr
    ⟨otherFuel, otherReadFuel, two⟩
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at left right
      exact SourceEqualityRequiredExecution.children_unique left right

/-- Initial Scan invariants derive the receipt for its supplied required return. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values results : List (Value Symbol Guard)}
    {classes selected : Constraints} {before middle : Checked width} {fourth savedFourth : Fourth}
    (scan : Scan budget unconstrained reaches values classes before fourth none selected middle savedFourth)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before fourth)
    {fuel readFuel : Nat} {heap : State Symbol Guard}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
      values middle.native.machine.heap = .done results heap) :
    ∃ next, SourceCurrentConjunctionRequired.Receipt formulas solver next selected values results
      middle (advanceHeap middle heap) := by
  obtain ⟨next, chosen, returned, receipt, _⟩ :=
    SourceCurrentConjunctionRequired.scan_required_complete formulas solver inventory scan ready admitted available
      proper active correct ranges
  obtain ⟨bound, readBound, enough⟩ := receipt.stable
  have chosenDone := enough bound readBound (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨sameValue, sameHeap⟩ := required_unique chosenDone actual
  cases sameValue
  cases sameHeap
  exact ⟨next, receipt⟩

end MicroCFTA.SourceCurrentConjunctionRequiredActual
