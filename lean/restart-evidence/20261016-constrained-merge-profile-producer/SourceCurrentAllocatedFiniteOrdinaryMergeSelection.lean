import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection

/-!
# Exact selection effects for ordinary Merge columns

An ordinary column contains no recursive cover candidates.
Selection therefore removes duplicate identities without changing the heap.
The result holds at every comparison fuel, including zero.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeSelection
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open MergedPhysicalGroupColumns (closedMu)
open MergedSourceComparison (Result)
variable {Symbol Guard : Type}

private theorem no_recursive (value : Value Symbol Guard) {rows arity : Nat}
    (profile : NodeShape rows arity value) : closedMu value = false := by
  cases NodeShape.domain value profile <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem retain (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) {rows arity : Nat} (profile : ChildrenShape rows arity inputs) :
    SourceMergedSelection.retain clear fuel [] inputs before = .done inputs before := by
  induction inputs with
  | nil => rfl
  | cons first rest ih =>
      simp only [SourceMergedSelection.retain, no_recursive first profile.1,
        Bool.false_eq_true, ite_false, SourceMergedSelection.anyAccepts, MergedSourceComparison.Result.bind,
        ih profile.2]

/-- Every comparison bound returns the literal distinct ordinary inputs at the same heap. -/
theorem select (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) {rows arity : Nat} (profile : ChildrenShape rows arity inputs) :
    SourceMergedSelection.select clear fuel inputs before = .done (distinctNodes inputs) before := by
  have recursive : inputs.filter closedMu = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro value member
    rw [no_recursive value (ChildrenShape.member inputs profile value member)]
    decide
  simp only [SourceMergedSelection.select, recursive, retain clear fuel inputs before profile,
    MergedSourceComparison.Result.bind]

/-- A supplied ordinary selection return identifies both its result and its entire heap. -/
theorem done {clear : Guard → Bool} {fuel : Nat} {inputs values : List (Value Symbol Guard)}
    {before after : State Symbol Guard} {rows arity : Nat} (profile : ChildrenShape rows arity inputs)
    (actual : SourceMergedSelection.select clear fuel inputs before = .done values after) :
    values = distinctNodes inputs ∧ after = before := by
  rw [select clear fuel inputs before profile] at actual
  obtain ⟨same, heap⟩ := Result.done.inj actual
  exact ⟨same.symm, heap.symm⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeSelection
