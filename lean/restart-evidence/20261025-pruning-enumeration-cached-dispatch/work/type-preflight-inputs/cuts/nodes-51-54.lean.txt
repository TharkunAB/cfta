theorem lookupNode_keeps (before after : State Symbol Guard)
    (kept : SourceEqualityRequiredCache.Keeps before after)
    (node : Nat) (value : Value Symbol Guard)
    (present : lookupNode before node = some value) : lookupNode after node = some value := by
