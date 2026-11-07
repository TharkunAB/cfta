import MicroCFTA.SourceSizedDeterminizationOrderedStep
import MicroCFTA.SourceSizedDeterminizationRun
import MicroCFTA.SourceSizedDeterminizationRows

/-!
# Bounded discovery with ordered token and tuple batches

Each batch reads tokens and tuples in their source order. Pending keys
use ascending set readback. The controller represents known sets by a
distinct discovery list. Its membership and length represent the source
set's membership and cardinality. The context keeps all emitted batches,
including the final batch. Output target-map grouping remains separate.

The existing round proof transfers through the computed permutations.
No caller supplies a coverage invariant or a completed output graph.
The bound counts checking rounds. It does not bound total tuple work.
-/
namespace MicroCFTA.SourceSizedDeterminizationOrderedRun
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationClosure
open SourceSizedDeterminizationDiscovery Std
attribute [local instance] lexOrd

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
  [Ord State] [Ord Symbol]

/-- Read the current found map's distinct target keys in ascending order. -/
def foundKeys (states : List State) (rows : Automaton State Symbol)
    (choices : List (Choice State Symbol)) : List (List State) :=
  CanonicalClasses.sortedSet (SourceSizedDeterminizationRun.targets states rows choices)

omit [Ord Symbol] in
/-- Found keys are exactly targets of choices in the current batch. -/
theorem mem_foundKeys (states : List State) (rows : Automaton State Symbol)
    (choices : List (Choice State Symbol)) (key : List State) :
    key ∈ foundKeys states rows choices ↔
      ∃ choice ∈ choices, target states rows choice.1 choice.2 = key := by
  simp only [foundKeys, CanonicalClasses.mem_sortedSet,
    SourceSizedDeterminizationRun.targets, List.mem_map]

/-- The initial ordered batch emits leaf transitions. -/
def initial (states : List State) (rows : Automaton State Symbol) : List (Choice State Symbol) :=
  SourceSizedDeterminizationOrderedStep.round states rows [] (SourceSizedDeterminizationRun.holders []) []

/-- Append an ordered batch and read its found map's ascending keys. -/
def step (states : List State) (rows : Automaton State Symbol)
    (new known : List (List State)) (choices : List (Choice State Symbol)) :
    List (List State) × List (Choice State Symbol) :=
  let batch := SourceSizedDeterminizationOrderedStep.round states rows new
    (SourceSizedDeterminizationRun.holders known) known
  (foundKeys states rows batch, choices ++ batch)

/-- The original limit supplies the complete discovery recursion bound. -/
def compile (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    Outcome (List State) (List (Choice State Symbol)) :=
  run limit (step states rows) limit [] (foundKeys states rows (initial states rows)) (initial states rows)

omit [Ord State] [Ord Symbol] in
private theorem reindex (states : List State) (rows : Automaton State Symbol)
    (known beforePending afterPending : List (List State))
    (beforeChoices afterChoices : List (Choice State Symbol))
    (invariant : Invariant states rows known beforePending beforeChoices)
    (permutation : afterChoices.Perm beforeChoices)
    (pending : ∀ key, key ∈ afterPending ↔ key ∈ beforePending) :
    Invariant states rows known afterPending afterChoices := by
  refine ⟨?_, ?_, ?_, permutation.nodup_iff.mpr invariant.distinct, invariant.keyDistinct⟩
  · intro state present edge stored keys related
    exact permutation.mem_iff.mpr (invariant.covered state present edge stored keys related)
  · intro choice present key child
    exact invariant.children choice (permutation.mem_iff.mp present) key child
  · intro choice present
    rcases invariant.targets choice (permutation.mem_iff.mp present) with knownKey | pendingKey
    · exact Or.inl knownKey
    · exact Or.inr ((pending _).mpr pendingKey)

/-- Ordered leaf emission establishes the full initial discovery invariant. -/
theorem initial_invariant (states : List State) (rows : Automaton State Symbol) :
    Invariant states rows [] (foundKeys states rows (initial states rows)) (initial states rows) := by
  have permutation := SourceSizedDeterminizationOrderedStep.round_perm
    states rows [] (SourceSizedDeterminizationRun.holders []) []
  apply reindex states rows [] _ _ _ _
    (SourceSizedDeterminizationRun.initial_invariant states rows) permutation
  intro key
  exact (CanonicalClasses.mem_sortedSet _ _).trans
    ((permutation.map (fun choice => target states rows choice.1 choice.2)).mem_iff)

/-- Ordered source batches retain coverage, declared children, and distinct choices. -/
theorem advance (states : List State) (rows : Automaton State Symbol)
    (known found : List (List State)) (choices : List (Choice State Symbol))
    (invariant : Invariant states rows known found choices) (nonempty : fresh known found ≠ []) :
    Invariant states rows (known ++ fresh known found)
      (step states rows (fresh known found) (known ++ fresh known found) choices).1
      (step states rows (fresh known found) (known ++ fresh known found) choices).2 := by
  have permutation := SourceSizedDeterminizationOrderedStep.round_perm
    states rows (fresh known found)
      (SourceSizedDeterminizationRun.holders (known ++ fresh known found)) (known ++ fresh known found)
  apply reindex states rows (known ++ fresh known found) _ _ _ _
    (SourceSizedDeterminizationRun.advance states rows known found choices invariant nonempty)
    ((List.Perm.refl choices).append permutation)
  intro key
  exact (CanonicalClasses.mem_sortedSet _ _).trans
    ((permutation.map (fun choice => target states rows choice.1 choice.2)).mem_iff)

/-- Every successful ordered evaluation derives its final closed table. -/
theorem evaluation_closed (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known found : List (List State)) (choices : List (Choice State Symbol))
    (calls : Nat) (result : Outcome (List State) (List (Choice State Symbol)))
    (execution : Evaluation limit (step states rows) known found choices calls result)
    (finalKnown : List (List State)) (finalChoices : List (Choice State Symbol))
    (returned : result = .ready finalKnown finalChoices)
    (invariant : Invariant states rows known found choices) :
    Closed states rows finalKnown finalChoices := by
  revert invariant
  induction execution with
  | limit_exceeded => cases returned
  | done within empty =>
      intro invariant
      cases returned
      exact SourceSizedDeterminizationRun.finish states rows _ _ _ invariant empty
  | next within nonempty following ih =>
      intro invariant
      exact ih returned (advance states rows _ _ _ invariant nonempty)

/-- Ordered concrete discovery evaluates within the limit plus one checking rounds. -/
theorem compile_complete (limit : Nat) (states : List State) (rows : Automaton State Symbol) :
    ∃ calls, calls ≤ limit + 1 ∧
      Evaluation limit (step states rows) [] (foundKeys states rows (initial states rows))
        (initial states rows) calls (compile limit states rows) ∧
      compile limit states rows ≠ .exhausted :=
  SourceSizedDeterminizationDiscovery.complete limit (step states rows)
    (foundKeys states rows (initial states rows)) (initial states rows)

/-- Successful ordered execution supplies closure without a caller loop invariant. -/
theorem compile_closed (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) : Closed states rows known choices := by
  obtain ⟨calls, _, execution, _⟩ := compile_complete limit states rows
  exact evaluation_closed limit states rows [] _ _ calls _ execution known choices returned
    (initial_invariant states rows)

/-- Ordered discovery preserves the original language at every Left state. -/
theorem compile_language (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) (state : State) (term : Term Symbol) :
    Accepts (SourceSizedDeterminizationRows.rows states rows choices) (.inl state) term ↔
      Accepts rows state term :=
  SourceSizedDeterminizationRows.left_accepts_iff states rows plain supported known choices
    (compile_closed limit states rows known choices returned) state term

/-- Ordered discovery gives unique size classes on the full Left/Right graph. -/
theorem compile_unique (limit : Nat) (states : List State) (rows : Automaton State Symbol)
    (plain : Decoder.Plain rows)
    (supported : ∀ state edge, edge ∈ rows state → state ∈ states)
    (known : List (List State)) (choices : List (Choice State Symbol))
    (returned : compile limit states rows = .ready known choices) :
    SizedRank.Unambiguous (SourceSizedDeterminizationRows.rows states rows choices) :=
  SourceSizedDeterminizationRows.classes_unique states rows plain supported choices
    (compile_closed limit states rows known choices returned).distinct

end MicroCFTA.SourceSizedDeterminizationOrderedRun
