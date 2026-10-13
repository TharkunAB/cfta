import MicroCFTA.Language

/-!
# The recursive merge counterexample

Let A accept a or f(A), and let B accept b or f(B). Their exposed union has
two f edges. Merging that group requests the child union [A, B]. Before the
repair, that child union requested the original merge again. This file records
that mandatory call cycle and the repaired finite dependency tree. It does not
claim termination of the full equality fixed-point schedule.
-/
namespace MicroCFTA.MergedAlternativesRecursion

/-- The two recursive operands and their exposed ordinary union. -/
inductive Node where
  | left | right | joined
  deriving DecidableEq, Repr

/-- Concrete labels for the smallest productive recursive counterexample. -/
inductive Symbol where
  | a | b | f
  deriving DecidableEq, Repr

/-- The closed edge view of A, B, and their source union. -/
def edges : Node → List (Symbol × List Node)
  | .left => [(.a, []), (.f, [.left])]
  | .right => [(.b, []), (.f, [.right])]
  | .joined => [(.a, []), (.f, [.left]), (.b, []), (.f, [.right])]

/-- The child column of the f/1 group in this counterexample. -/
def childColumn : List Node :=
  ((edges .joined).filter (fun edge => edge.1 == .f)).flatMap Prod.snd

/-- Grouping the exposed union reproduces the same two recursive operands. -/
theorem childColumn_eq : childColumn = [.left, .right] := rfl

/-- Both source operands are recursive boundaries and remain in the child filter. -/
def recursive : Node → Bool
  | .left | .right => true
  | .joined => false

/-- The repaired guard recognizes the exact column that caused re-entry. -/
theorem column_has_boundary : childColumn.any recursive = true := rfl

/-- The two mandatory call sites in the original source dependency cycle. -/
inductive Task where
  | mergeJoined | combineColumn
  deriving DecidableEq, Repr

/-- Required recursive calls for this source execution, before or after the repair. -/
def requests (repaired : Bool) : Task → List Task
  | .mergeJoined => [.combineColumn]
  | .combineColumn => if repaired && childColumn.any recursive then [] else [.mergeJoined]

/-- A completed evaluation has a finite tree of completed required calls. -/
inductive Completes (requests : Task → List Task) : Task → Prop where
  | done : (∀ next ∈ requests task, Completes requests next) → Completes requests task

/-- Every legacy call site requires the other call site. -/
theorem legacy_dependency (task : Task) :
    ∃ next, next ∈ requests false task := by
  cases task <;> simp [requests]

/-- The original merge cannot have a finite evaluation tree on this input. -/
theorem legacy_no_completion (task : Task) : ¬Completes (requests false) task := by
  intro completed
  induction completed with
  | @done task children ih =>
      obtain ⟨next, required⟩ := legacy_dependency task
      exact ih next required

/-- The repaired child-union branch returns without repeating the merge call. -/
theorem repaired_column : Completes (requests true) .combineColumn := by
  apply Completes.done
  simp [requests, column_has_boundary]

/-- The repaired execution has a finite two-node dependency tree. -/
theorem repaired_completion : Completes (requests true) .mergeJoined := by
  apply Completes.done
  intro next required
  have same : next = .combineColumn := by simpa [requests] using required
  subst next
  exact repaired_column

end MicroCFTA.MergedAlternativesRecursion
