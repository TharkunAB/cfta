  have grownFlags : ∀ (slot : Nat),
    candidate nextHeap ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot) := by
    intro slot
    specialize flags slot
    generalize slotValueSame : ((before.core.values[slot]?).getD .eliminated) = slotValue at flags ⊢
    clear slotValueSame
    cases slotValue with
    | enumerated _ => exact flags
    | eliminated => exact flags
    | unenumerated node scs =>
      cases node with
      | none => exact flags
      | some oldHandle =>
        cases oldLookup : lookupNode heap oldHandle with
        | none =>
          simp only [candidate, oldLookup, Option.map_none] at flags
          cases flags
        | some oldValue =>
          simpa only [candidate, oldLookup,
            lookupNode_keeps heap nextHeap kept oldHandle oldValue oldLookup, Option.map_some] using flags
