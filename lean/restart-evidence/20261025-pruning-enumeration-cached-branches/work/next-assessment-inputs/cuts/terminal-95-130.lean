/-- Initial pending inputs and current bounds derive the complete terminal arm. -/
theorem run_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before) (paths : Roots before.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.values waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.counter)
    (pending : InputsPending before (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (nonempty : incoming ≠ .empty)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingBounded : ∀ sc ∈ incomingScs, sc.var < before.counter)
    (ranges : ∀ (prefixFuel : Nat) (recorded : List Nat) (winner : Nat)
      (moved : EnumerationWaitingIndex.Waiting) (joined : EnumerationState.State Symbol EnumGuard),
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run prefixFuel first rest waiting before) =
        [.ok ((recorded, winner, moved), joined)] →
      SourcePruningEnumerationFold.Ranges checkEmpty recorded beforeCaller joined winner memos.query ∧
      ∀ (foldFuel P H : Nat) (foldCaller : Caller width)
        (folded : EnumerationState.State Symbol EnumGuard) (foldQueries : Queries),
        SourcePruningEnumerationFold.run checkEmpty foldFuel P H recorded beforeCaller joined winner memos.query =
          (.ok (some [.ok ((), folded)]), foldCaller, foldQueries, folded) →
        match folded.values[winner]? with
        | some (.unenumerated (some oldHandle) _) =>
            match lookupNode foldCaller.checked.native.machine.heap oldHandle with
            | some old => SourceCurrentAllocatedNativeRequestBounds.WordRanges
                (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                foldCaller.checked
            | none => True
        | _ => True) :
