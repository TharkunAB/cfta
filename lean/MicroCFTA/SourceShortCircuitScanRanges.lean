import MicroCFTA.SourceShortCircuitScan

/-!
# Resource contracts on actual short-circuit scans

A local resource implication transfers through the exact reached suffixes.
The proof retains the actual state invariant after each continuing callback.
-/
namespace MicroCFTA.SourceShortCircuitScan

/-- Reached resource checks imply another scan contract when actual continuing calls retain the invariant. -/
theorem Ranges.transfer (continueOn : Bool) (step : Query → State → Bool → State → Prop)
    (first second : Query → State → Prop) (invariant : State → Prop)
    (convert : ∀ query state, invariant state → first query state → second query state)
    (retain : ∀ query state after, invariant state → first query state → step query state continueOn after → invariant after)
    (queries : List Query) (state : State) (valid : invariant state) (ranges : Ranges continueOn step first queries state) :
    Ranges continueOn step second queries state := by
  induction queries generalizing state with
  | nil => trivial
  | cons query rest ih =>
      refine ⟨convert query state valid ranges.1, ?_⟩
      intro after actual
      exact ih after (retain query state after valid ranges.1 actual) (ranges.2 after actual)

end MicroCFTA.SourceShortCircuitScan
