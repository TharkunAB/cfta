theorem decision_none_iff (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached) :
    decision stop order metadata before = none ↔
      ∃ rule, stop = some rule ∧ candidates before ≠ [] ∧
        ∀ uv ∈ candidates before, rule metadata uv = true := by
