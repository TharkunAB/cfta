import MicroCFTA.EnumerationState

namespace MicroCFTA.EqualityTrieVariableOrigin

/-- Each descended constraint retains a variable from an input constraint. -/
theorem descendScs_origin (index : Nat) (scs : List EnumerationState.Suspended)
    (out : EnumerationState.Suspended)
    (member : out ∈ EnumerationState.descendScs index scs) :
    ∃ original ∈ scs, out.var = original.var := by
  simp_all [EnumerationState.descendScs, EqualityTrie.descendScs] <;> grind

/-- Descending constraints preserves an upper bound on their variables. -/
theorem descendScs_preserves_below (index bound : Nat)
    (scs : List EnumerationState.Suspended)
    (bounded : ∀ sc ∈ scs, sc.var < bound) :
    ∀ sc ∈ EnumerationState.descendScs index scs, sc.var < bound := by
  intro sc member
  obtain ⟨original, present, same⟩ := descendScs_origin index scs sc member
  rw [same]
  exact bounded original present

end MicroCFTA.EqualityTrieVariableOrigin
