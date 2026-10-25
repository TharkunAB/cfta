noncomputable def run
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard))))) ×
      Caller width × Queries × EnumerationState.State Symbol EnumGuard :=
  match sources with
  | [] => (.ok (some [.ok ((), before)]), beforeCaller, queries, before)
  | source :: rest =>
    let observation :
      (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
        SourceCurrentAllocatedConjunctionWorker.Outcome width)
        (Option (EnumerateM Symbol EnumGuard Unit))) × Caller width × Queries :=
      SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h beforeCaller before source target queries
    match observation with
    | (.error fault, reachedCaller, savedQueries) => (.error fault, reachedCaller, savedQueries, before)
    | (.ok none, reachedCaller, savedQueries) => (.ok none, reachedCaller, savedQueries, before)
    | (.ok (some action), reachedCaller, savedQueries) =>
        let raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)) := ExceptT.run (action before)
        match raw with
        | [.ok ((), after)] => run checkEmpty nativeFuel p h rest reachedCaller after target savedQueries
        | other => (.ok (some other), reachedCaller, savedQueries, before)

/-- Every reached decoded request fits the fixed machine width. -/
def Ranges
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries) : Prop :=
  match sources with
  | [] => True
  | source :: rest =>
      (if source = target then True else
        match before.values[source]?, before.values[target]? with
        | some (.unenumerated (some left) _), some (.unenumerated (some right) _) =>
            match lookupNode beforeCaller.checked.native.machine.heap left,
                lookupNode beforeCaller.checked.native.machine.heap right with
            | some first, some second => SourceCurrentAllocatedNativeRequestBounds.WordRanges
                (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain first second))
                beforeCaller.checked
            | _, _ => True
        | _, _ => True) ∧
      ∀ nativeFuel p h action afterCaller saved after,
        SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
          beforeCaller before source target queries = (.ok (some action), afterCaller, saved) →
        ExceptT.run (action before) = [.ok ((), after)] →
        Ranges checkEmpty rest afterCaller after target saved

