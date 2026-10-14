import MicroCFTA.SourceSizedBoundedReference

/-!
# Complete public queries for a bounded canonical sequence

The actual fromClasses record reads the returned bounded classes. Their
canonical order supplies a bounded reference graph. Exact membership at
the original language then derives every common query law.
-/
namespace MicroCFTA.SourceSizedBoundedApiLaws
open Language RecursiveSize SourceSizedReference SourceSizedDispatcher

/-- The source fromClasses record reads the same sequence in all four queries. -/
def fromClasses [DecidableEq Symbol] (classes : Nat → List (Term Symbol)) : Api Symbol where
  terms := SourceSizedQueries.termsSigned classes
  count := SourceSizedQueries.countSigned classes
  unrank := SourceSizedQueries.unrankSigned classes
  rank := SourceSizedQueries.rank classes nodeSize

/-- Canonical bounded order identifies the complete record with one reference graph. -/
theorem reference_eq [DecidableEq Symbol] (A : Automaton State Symbol) (root : State) (bound : Int)
    (terms : Nat → List (Term Symbol))
    (sequence : ∀ size, terms size = if size ≤ bound.toNat then classes A size root else []) :
    fromClasses terms = referenceApi (SourceSizedBoundedReference.rows A bound) root := by
  have same : terms = fun size => classes (SourceSizedBoundedReference.rows A bound) size root := by
    funext size
    rw [sequence, SourceSizedBoundedReference.classes_eq]
    cases size with
    | zero => simp [classes_zero]
    | succ remaining =>
        have within : remaining + 1 ≤ bound.toNat ↔ ((remaining + 1 : Nat) : Int) ≤ bound := by omega
        simp only [within]
  rw [same]
  rfl

/-- Actual bounded classes satisfy all exact query laws for the original bounded language. -/
theorem exact [DecidableEq Symbol] (A : Automaton State Symbol) (root : State) (bound : Int)
    (terms : Nat → List (Term Symbol)) (language : Term Symbol → Prop)
    (sequence : ∀ size, terms size = if size ≤ bound.toNat then classes A size root else [])
    (membership : ∀ size term, term ∈ terms size ↔ language term ∧ nodeSize term = size ∧ (size : Int) ≤ bound) :
    SourceSizedApiLaws.Exact (fromClasses terms) (fun term => language term ∧ (nodeSize term : Int) ≤ bound) := by
  rw [reference_eq A root bound terms sequence]
  apply SourceSizedApiLaws.reference
  intro term
  have source := membership (nodeSize term) term
  have same := reference_eq A root bound terms sequence
  have natural : terms (nodeSize term) =
      classes (SourceSizedBoundedReference.rows A bound) (nodeSize term) root := by
    have field := congrArg (fun api => api.terms (nodeSize term : Int)) same
    have zero : terms 0 = [] := by rw [sequence]; simp [classes_zero]
    simpa only [fromClasses, referenceApi, SourceSizedQueries.termsSigned_nat terms zero,
      SourceSizedQueries.termsSigned_nat
        (fun size => classes (SourceSizedBoundedReference.rows A bound) size root)
        (classes_zero (SourceSizedBoundedReference.rows A bound) root)] using field
  rw [natural, mem_classes_iff] at source
  simpa only [and_true, true_and] using source

end MicroCFTA.SourceSizedBoundedApiLaws
