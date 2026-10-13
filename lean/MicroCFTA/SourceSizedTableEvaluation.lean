import MicroCFTA.SourceSizedPreprocessing

/-!
# Finite evaluation of optimized exact-size tables

The count and compiled-plan recurrences read only smaller child sizes.
This certificate records those finite recursive evaluations directly. It
does not infer their execution from equality with a reference term list.
The finite folds, arithmetic, and plan decoder are total Lean operations.
The bound counts nested table queries, not primitive runtime instructions.
Concrete Haskell lazy heap evaluation remains a separate correspondence.
-/

namespace MicroCFTA.SourceSizedTableEvaluation

open Language RecursiveSize SourceSizedDecided SourceSizedDispatcher
open SourceSizedPreprocessing SourceObservations SourceSymbolicIndex
attribute [local instance] lexOrd

/-- A completed count and plan query records every possible smaller child query. -/
inductive Evaluation (A : Automaton State Symbol) :
    Nat → Nat → State → Nat → Decoder.Plan (Term Symbol) → Prop where
  | zero (fuel : Nat) (state : State) : Evaluation A (fuel + 1) 0 state 0 (.source [])
  | step (fuel remaining : Nat) (state : State)
      (counts : Nat → State → Nat) (plans : Nat → State → Decoder.Plan (Term Symbol))
      (finished : ∀ edge ∈ A state, ∀ child ∈ edge.children, ∀ childSize,
        childSize ≤ remaining → Evaluation A fuel childSize child
          (counts childSize child) (plans childSize child)) :
      Evaluation A (fuel + 1) (remaining + 1) state
        ((A state).map (fun edge => forestCounts
          (fun childSize child => if childSize ≤ remaining then counts childSize child else 0)
          edge.children remaining)).sum
        (Decoder.choices ((A state).map (fun edge =>
          .map (Term.node edge.label) (forestPlans
            (fun childSize child => if childSize ≤ remaining then plans childSize child else .source [])
            edge.children remaining))))

/-- Every optimized count/plan query has a finite derivation despite cycles in the state graph. -/
theorem finite (A : Automaton State Symbol) (fuel size : Nat) (within : size ≤ fuel) (state : State) :
    Evaluation A (fuel + 1) size state (countAt A size state) (compileAt A size state) := by
  induction fuel generalizing size state with
  | zero =>
      have zero : size = 0 := by omega
      subst size
      simpa only [countAt, compileAt] using (Evaluation.zero (A := A) 0 state)
  | succ fuel ih =>
      cases size with
      | zero => simpa only [countAt, compileAt] using (Evaluation.zero (A := A) (fuel + 1) state)
      | succ remaining =>
          rw [countAt, compileAt]
          apply Evaluation.step
          intro edge member child childMember childSize smaller
          exact ih childSize (by omega) child

/-- Node count plus one bounds the recursive count/plan query nesting. -/
theorem finite_bound (A : Automaton State Symbol) (size : Nat) (state : State) :
    Evaluation A (size + 1) size state (countAt A size state) (compileAt A size state) :=
  finite A size size (Nat.le_refl _) state

/-- The finite optimized computation returns the exact distinct reference count and decoder. -/
theorem exact_finite [DecidableEq State] [DecidableEq Symbol]
    (A : Automaton State Symbol) (plain : Decoder.Plain A)
    (states : List State) (complete : ∀ state, state ∈ states)
    (passed : SourceSizedDispatchGraph.unambiguousRows A states complete = true)
    (size : Nat) (state : State) :
    Evaluation A (size + 1) size state (countAt A size state) (compileAt A size state) ∧
    countAt A size state = (SourceSizedReference.classes A size state).length ∧
    ∀ rank, Decoder.decode (compileAt A size state) rank =
      (SourceSizedReference.classes A size state)[rank]? := by
  have same := SourceSizedReference.classes_eq_enumerate A plain
    (SourceSizedDispatchGraph.gate_unique A plain states complete passed) size state
  refine ⟨finite_bound A size state, ?_, ?_⟩
  · rw [countAt_correct, same]
  · intro rank
    rw [Decoder.decode_correct, values_compileAt, same]

/-- Actual preprocessing and the product gate both finish before finite optimized class queries. -/
theorem public_components [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula)) :
    (∃ classes, CanonicalClasses.canonical (graph input) = some classes ∧
      sortedRows input = sortRows input classes) ∧
    (∃ fuel, MinimumSize.sweep
        (Language.intersect (ordinaryRows (sortedRows input)) (ordinaryRows (sortedRows input)))
        (SourceSizedDispatchGraph.pairs input.states)
        (MinimumSize.sweeps
          (Language.intersect (ordinaryRows (sortedRows input)) (ordinaryRows (sortedRows input)))
          (SourceSizedDispatchGraph.pairs input.states) fuel (fun _ => none)) =
      MinimumSize.sweeps
        (Language.intersect (ordinaryRows (sortedRows input)) (ordinaryRows (sortedRows input)))
        (SourceSizedDispatchGraph.pairs input.states) fuel (fun _ => none)) ∧
    ∀ size state, Evaluation (ordinaryRows (sortedRows input)) (size + 1) size state
      (countAt (ordinaryRows (sortedRows input)) size state)
      (compileAt (ordinaryRows (sortedRows input)) size state) :=
  ⟨sortedRows_completed input,
    SourceSizedDispatchGraph.gate_minimum_terminates _ input.states input.complete,
    fun size state => finite_bound _ size state⟩

end MicroCFTA.SourceSizedTableEvaluation
