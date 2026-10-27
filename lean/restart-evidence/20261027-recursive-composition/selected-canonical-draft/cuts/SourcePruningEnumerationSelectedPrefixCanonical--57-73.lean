theorem prepared_nonempty_canonical {Typing Key : Type}
    [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → InternedConstructorTemplates.Value Symbol Constraint → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : InternedConstructorTemplates.Value Symbol Constraint)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit)
    (checked after : EnumerationState.State Symbol Constraint)
    (canonical : Canonical checked) (valid : ValidSuspended scs)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) : Canonical after := by
