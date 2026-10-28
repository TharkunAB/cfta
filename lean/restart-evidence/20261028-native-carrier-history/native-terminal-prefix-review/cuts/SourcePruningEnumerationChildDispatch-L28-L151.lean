noncomputable def observe
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting) (queries : Queries) : Observation width :=
  if incoming = .empty then
    (.ok (some []), beforeCaller, queries, before, waiting)
  else
    match scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | ([], _) =>
        match SourcePruningEnumerationShallowChild.prepareChild scs incoming with
        | none => (.ok none, beforeCaller, queries, before, waiting)
        | some action => (.ok (some (ExceptT.run (action before))), beforeCaller, queries, before, waiting)
    | (first :: rest, descendants) =>
        SourcePruningEnumerationTerminal.run checkEmpty representativeFuel nativeFuel p h
          first rest waiting beforeCaller before incoming descendants queries

/-- Add the native cache while retaining terminal caller, query and raw effects. -/
noncomputable def run
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) : Observation width × Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  if incoming = .empty then
    ((.ok (some []), beforeCaller, queries, before.core, before.waiting), some before)
  else
    match scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | ([], _) =>
        (observe checkEmpty representativeFuel nativeFuel p h scs incoming
          beforeCaller before.core before.waiting queries,
          match SourcePruningEnumerationCachedPrepare.prepareChild
              beforeCaller.checked.native.machine.heap indexFuel scs incoming before with
          | some [] => some before
          | some [(_, after)] => some after
          | _ => none)
    | (first :: rest, descendants) =>
        SourcePruningEnumerationCachedTerminalAdapter.run
          checkEmpty representativeFuel nativeFuel p h indexFuel
          first rest beforeCaller before incoming descendants queries

/-- Cache erasure preserves every raw result and reached caller at fixed bounds. -/
theorem erase
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) :
    (run checkEmpty representativeFuel nativeFuel p h indexFuel
      scs incoming beforeCaller before queries).1 =
      observe checkEmpty representativeFuel nativeFuel p h scs incoming
        beforeCaller before.core before.waiting queries := by
  by_cases empty : incoming = .empty
  · simp only [run, observe, ite_eq_left empty]
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil => simp only [run, ite_eq_right empty, partitioned]
      | cons first rest =>
        simpa only [run, observe, ite_eq_right empty, partitioned] using
          SourcePruningEnumerationCachedTerminalAdapter.erase
            checkEmpty representativeFuel nativeFuel p h indexFuel
            first rest beforeCaller before incoming descendants queries

/-- The terminal route retains the complete existing adapter and all its receipts. -/
theorem terminal
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) (first : Suspended) (rest descendants : List Suspended)
    (partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants)) :
    run checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming beforeCaller before queries =
      SourcePruningEnumerationCachedTerminalAdapter.run
        checkEmpty representativeFuel nativeFuel p h indexFuel
        first rest beforeCaller before incoming descendants queries := by
  by_cases empty : incoming = .empty
  · simp only [run, SourcePruningEnumerationCachedTerminalAdapter.run, ite_eq_left empty]
  · simp only [run, ite_eq_right empty, partitioned]

/-- Every successful singleton cache has the actual raw row core at fixed bounds. -/
theorem singleton_core
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller reachedCaller : Caller width)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries savedQueries : Queries) (fragment : Fragments.Fragment Symbol)
    (returned outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting)
    (observed : run checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming
      beforeCaller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    after.core = returned := by
  by_cases empty : incoming = .empty
  · simp [run, empty] at observed
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | cons first rest =>
        apply SourcePruningEnumerationCachedTerminalAdapter.singleton_core checkEmpty
          representativeFuel nativeFuel p h indexFuel first rest beforeCaller reachedCaller
          before after incoming descendants queries savedQueries fragment returned outer waiting
        simpa only [run, ite_eq_right empty, partitioned] using observed
      | nil =>
        cases cached : SourcePruningEnumerationCachedPrepare.prepareChild
            beforeCaller.checked.native.machine.heap indexFuel scs incoming before with
        | none => simp only [run, ite_eq_right empty, partitioned, cached, Prod.mk.injEq,
            reduceCtorEq, and_false] at observed
        | some rows =>
          have erasure := SourcePruningEnumerationCachedPrepare.erase_some
            beforeCaller.checked.native.machine.heap indexFuel scs incoming before rows cached
          cases prepared : SourcePruningEnumerationShallowChild.prepareChild
              (EnumGuard := Constraint) scs incoming with
          | none => simp only [prepared, Option.map_none, reduceCtorEq] at erasure
          | some action =>
            have raw := congrArg (fun result => result.1.1) observed
            simp only [run, observe, ite_eq_right empty, partitioned, prepared] at raw
            simp only [prepared, Option.map_some, Option.some.injEq] at erasure
            have rowsSame : rows.map (fun row => Except.ok (row.1, row.2.core)) =
                [.ok (fragment, returned)] :=
              erasure.symm.trans (Option.some.inj (Except.ok.inj raw))
            obtain ⟨row, singleton, mapped⟩ := List.map_eq_singleton_iff.mp rowsSame
            rcases row with ⟨childFragment, childCache⟩
            subst rows
            have cacheSame : childCache = after := by
              simpa only [run, ite_eq_right empty, partitioned, cached, Option.some.injEq] using
