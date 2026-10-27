theorem prepared_action
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle) :
    SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap =
      .done (value, some (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs))) nextHeap := by
  cases value with
  | empty => exact False.elim (nonempty rfl)
  | reference name => simp [encodeNode] at encoded
  | node entry edges depth free => simp only [SourcePruningEnumerationAction.prepare, narrowed, encoded]
  | union entry members depth free => simp only [SourcePruningEnumerationAction.prepare, narrowed, encoded]
  | mu entry body depth ordinary => simp only [SourcePruningEnumerationAction.prepare, narrowed, encoded]

/-- Successful preparation has one raw row at its actual reached core. -/
theorem prepared_singleton
