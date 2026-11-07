import MicroCFTA.SourceSizedDeterministic

/-!
# The current unambiguity check with its key shortcut

The source checks distinct symbol and ordered-child keys first. On failure
it builds the synchronous product and checks alternative overlap. Both
passing branches derive disjoint alternatives and distinct raw size classes.

This is the finite graph and container value calculation. Native Map/Set
storage, machine sizes, and total execution work remain separate.
-/
namespace MicroCFTA.SourceSizedCurrentUnambiguity
open Language

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

/-- Keep the source key-cardinality shortcut before the product overlap scan. -/
def unambiguousRows (rows : Automaton State Symbol) (states : List State)
    (complete : ∀ state, state ∈ states) : Bool :=
  SourceSizedDeterministic.bottomUpDeterministic rows states ||
    SourceSizedDispatchGraph.unambiguousRows rows states complete

/-- A passing key check accepts without requiring a product result. -/
theorem deterministic_shortcut (rows : Automaton State Symbol) (states : List State)
    (complete : ∀ state, state ∈ states)
    (passed : SourceSizedDeterministic.bottomUpDeterministic rows states = true) :
    unambiguousRows rows states complete = true := by
  simp [unambiguousRows, passed]

/-- A failed key check selects exactly the existing product overlap scan. -/
theorem product_after_failure (rows : Automaton State Symbol) (states : List State)
    (complete : ∀ state, state ∈ states)
    (failed : SourceSizedDeterministic.bottomUpDeterministic rows states = false) :
    unambiguousRows rows states complete =
      SourceSizedDispatchGraph.unambiguousRows rows states complete := by
  simp [unambiguousRows, failed]

/-- Either passing source branch separates all alternatives at each state. -/
theorem gate_disjoint (rows : Automaton State Symbol) (states : List State)
    (complete : ∀ state, state ∈ states)
    (passed : unambiguousRows rows states complete = true) (state : State) :
    RecursiveUnambiguous.DisjointRows rows state := by
  rcases Bool.or_eq_true_iff.mp passed with keys | product
  · exact SourceSizedDeterministic.gate_disjoint rows states
      (fun state _ _ => complete state) keys state
  · exact SourceSizedDispatchGraph.gate_disjoint rows states complete product state

/-- Plain rows and either passing branch derive distinct classes at every state. -/
theorem gate_unique (rows : Automaton State Symbol) (plain : Decoder.Plain rows)
    (states : List State) (complete : ∀ state, state ∈ states)
    (passed : unambiguousRows rows states complete = true) : SizedRank.Unambiguous rows := by
  rcases Bool.or_eq_true_iff.mp passed with keys | product
  · exact SourceSizedDeterministic.gate_unique rows plain states
      (fun state _ _ => complete state) keys
  · exact SourceSizedDispatchGraph.gate_unique rows plain states complete product

end MicroCFTA.SourceSizedCurrentUnambiguity
