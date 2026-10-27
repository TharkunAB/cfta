/-- A retained successful candidate exposes the actual action and index observations. -/
private theorem narrowed_observation
    (fuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (caller reached : Caller width) (before after : OldCached)
    (queries savedQueries : Queries) (readAfter checked : OldCore)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit)
    (right : Option (List (Except Error ((Bool × Metadata Typing) × OldCore))))
    (ordinary : Option
      (List (Except Error ((Nat × Nat × List Suspended × Node) × OldCore)) ×
        Option (SourcePruningEnumerationNativeBranches.Result width)))
    (reading : ExceptT.run (getValue fuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap fuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel
      uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (value, some action) heap)
    (encoded : encodeNode value = some newHandle)
    (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
      stop order metadata fuel fuel fuel fuel fuel fuel uv caller before queries =
      .narrowed checked (.done (value, some action) heap) reached savedQueries
        (some [.ok ((), after.core)]) (some after) right ordinary) :
    ExceptT.run (action checked) = [.ok ((), after.core)] ∧
      SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle scs
        before after.core = some after := by
