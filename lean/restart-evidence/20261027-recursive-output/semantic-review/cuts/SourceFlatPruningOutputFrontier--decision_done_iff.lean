theorem decision_done_iff (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (before : Cached) :
    decision stop order metadata before = some .done ↔ candidates before = [] := by
