def allocate
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (node : Option Nat) (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  (SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated node [])).map fun flag =>
    (before.core.counter,
      ⟨EnumerationState.allocated node before.core,
        fun slot => if flag then
          if slot = before.core.counter then true else before.expandable slot
          else before.expandable slot,
        before.waiting⟩)
