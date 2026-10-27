private theorem retained_action
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (fuel uv oldHandle : Nat) (scs : List Suspended) (oldValue value : Node)
    (caller reached : Caller width) (before after : Cached) (queries : SourceEndpointMemo.Memos)
    (readAfter checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (selectedAction : EnumerateM Symbol Constraint Unit)
    (preparedField : MergedSourceComparison.Result Symbol Constraint
      (Node × Option (EnumerateM Symbol Constraint Unit)))
    (right : Option (List (Except Error ((Bool × Metadata Typing) × Core))))
    (ordinary : Option (List (Except Error ((Nat × Nat × List Suspended × Node) × Core)) ×
      Option (SourcePruningEnumerationNativeBranches.Result width)))
    (reading : ExceptT.run (getValue fuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap fuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel uv oldHandle
      scs oldValue caller.checked.native.machine.heap = .done (value, some selectedAction) heap)
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before queries = .narrowed checked preparedField reached queries
        (some [.ok ((), after.core)]) (some after) right ordinary) :
    Success selectedAction checked () after.core := by
