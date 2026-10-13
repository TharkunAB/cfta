import MicroCFTA.SourceCyclicRowsReadback
import MicroCFTA.SourceRowsMinimum

/-!
# Minimum preparation and finite cyclic class execution

The source table computes minimum sizes before its shared count and decoder
tables. The finite-map convergence proof covers that prepass. The existing
size recurrence then bounds each count and plan query by node count plus
one. These certificates do not count primitive machine steps or prove native
intersection construction and lazy heap execution.
-/
namespace MicroCFTA.SourceCyclicRowsExecution
open Language SourceGuards SourceObservations SourceDenseRows RecursiveSize

variable {State : Type} {keys : List State}
  [DecidableEq State] [DecidableEq Formula] [DecidableEq Key] [Ord Key]
  (formulas : Formulas Formula) (solver : Entailment Formula) (input : SourceCyclicRows.Input keys Formula)
  (order : Label Formula → Key) (output : Automaton (Member keys) (Label Formula))
  (success : SourceCyclicRows.compile formulas solver input order = some (.ok output))

omit [DecidableEq State] [DecidableEq Formula] in
/-- The output row map has the exact finite domain already derived by the adapter. -/
theorem supported : SourceRowsMinimum.Supported output keys.attach := by
  intro state edge member
  simp

include success

/-- The actual minimum prepass converges and gives the original language's least node count. -/
theorem minimum_prepass :
    (∃ fuel, MinimumSize.sweeps output keys.attach fuel (fun _ => none) = SourceRowsMinimum.minimumSizes output keys.attach ∧
      MinimumSize.sweep output keys.attach (SourceRowsMinimum.minimumSizes output keys.attach) =
        SourceRowsMinimum.minimumSizes output keys.attach) ∧
    (∀ size, SourceRowsMinimum.minimumSizes output keys.attach input.root = some size ↔
      (∃ term, Accepts (SourceCyclicRows.original formulas solver input) input.root term ∧ nodeSize term = size) ∧
      (∀ term, Accepts (SourceCyclicRows.original formulas solver input) input.root term → size ≤ nodeSize term)) := by
  obtain ⟨plain, _, language⟩ := SourceCyclicRows.compile_exact formulas solver input order output success
  refine ⟨SourceRowsMinimum.terminates output keys.attach, ?_⟩
  intro size
  rw [SourceRowsMinimum.correct output plain keys.attach (supported output) input.root size]
  simp only [language]

/-- Minimum preparation and every exact-size count/plan query both finish in the source models. -/
theorem finite_query (size : Nat) :
    ∃ fuel, MinimumSize.sweeps output keys.attach fuel (fun _ => none) = SourceRowsMinimum.minimumSizes output keys.attach ∧
      MinimumSize.sweep output keys.attach (SourceRowsMinimum.minimumSizes output keys.attach) =
        SourceRowsMinimum.minimumSizes output keys.attach ∧
      SourceSizedTableEvaluation.Evaluation output (size + 1) size input.root
        (countAt output size input.root) (compileAt output size input.root) := by
  obtain ⟨fuel, reached, stable⟩ := (minimum_prepass formulas solver input order output success).1
  exact ⟨fuel, reached, stable, SourceSizedTableEvaluation.finite_bound output size input.root⟩

/-- No minimum entry is exactly the absence of every accepted finite source term. -/
theorem minimum_none : SourceRowsMinimum.minimumSizes output keys.attach input.root = none ↔
    ∀ term, ¬Accepts (SourceCyclicRows.original formulas solver input) input.root term := by
  obtain ⟨plain, _, language⟩ := SourceCyclicRows.compile_exact formulas solver input order output success
  rw [SourceRowsMinimum.none_iff output plain keys.attach (supported output) input.root]
  simp only [language]

end MicroCFTA.SourceCyclicRowsExecution
