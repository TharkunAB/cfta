import MicroCFTA.SourcePruningResumeRefutation

/-!
# Pending refutation under an assignment extension

Each pending entry retains its raw variable ID.
Assignments that agree at these bounded IDs retain the same refutation.
-/
namespace MicroCFTA.SourcePruningResume
open Language SourcePruningPartialMatch

variable {Symbol : Type} [DecidableEq Symbol]

/-- Agreement at every original pending ID preserves its exact refutation. -/
theorem refutes_assignment_congr (limit : Nat)
    (assignment extended : Nat → Term Symbol) (pending : Pending Symbol)
    (bounded : PendingBound limit pending)
    (agree : ∀ uv < limit, extended uv = assignment uv) :
    Refutes extended pending ↔ Refutes assignment pending := by
  unfold Refutes
  constructor
  · intro refuted matched
    apply refuted
    intro entry member
    rw [agree entry.2 (bounded entry member)]
    exact matched entry member
  · intro refuted matched
    apply refuted
    intro entry member
    rw [← agree entry.2 (bounded entry member)]
    exact matched entry member

end MicroCFTA.SourcePruningResume
