/-- Admit only reached parked or nonempty caches; retain Empty rejection and bounded ordinary observations. -/
def Valid
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv : Nat)
    (caller : Caller width) (before : Cached) (memos : Memos) : Result width Typing → Prop := fun result =>
  ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
    ExceptT.run (getValue readFuel uv before.core) = [.ok (.unenumerated (some oldHandle) scs, readAfter)] ∧
    match result with
    | .stopped _ _ => False
    | .parked checked candidate raw =>
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          checkFuel uv oldHandle scs readAfter) = [.ok (true, checked)] ∧
        ∃ after : Cached, candidate = some after ∧ after.core = checked ∧
          SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after ∧ Safe after.core ∧
          EnumerationReferences.PendingReferences after.core ∧ after.core.counter = before.core.counter ∧
          (∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
            EnumerationOrder.Stratified after.core level frontier) ∧
          raw = some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata after checked))
    | .narrowed checked prepared reached queries action candidate right ordinary =>
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)] ∧
        ∃ (oldValue value : Node) (heap : InternedConstructorTemplates.State Symbol Constraint)
          (selectedAction : EnumerateM Symbol Constraint Unit) (final : Memos),
          lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
          SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue
            caller.checked.native.machine.heap = .done value heap ∧
          SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
            uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (value, some selectedAction) heap ∧
          prepared = .done (value, some selectedAction) heap ∧
          reached = SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge ∧
          queries = memos.query ∧ Post formulas solver inventory caller reached final ∧ final.query = queries ∧
          ((value = .empty ∧ action = some [] ∧ candidate = none ∧ right = none ∧ ordinary = none) ∨
            ∃ (newHandle : Nat) (after : Cached), value ≠ .empty ∧ encodeNode value = some newHandle ∧
              action = some [.ok ((), after.core)] ∧ candidate = some after ∧
              SourcePruningEnumerationNativeBranchCompletion.CacheValid reached after ∧ Safe after.core ∧
              EnumerationReferences.PendingReferences after.core ∧ EnumerationDriver.Ready uv after.core ∧
              after.core.values[uv]? = some (.unenumerated (some newHandle) scs) ∧
              after.waiting = before.waiting ∧
              right = some [.ok ((false, metadata), after.core)] ∧
              ordinary = some (SourcePruningEnumerationNativeOrdinary.run
                checkEmpty r n p h k uv edgesOf reached after queries) ∧
              ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
                (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
                (free : List InternedBinderProtocol.Reference),
                value = .node parentEntry storedEdges depth free →
                scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false →
                (∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), edge ∈ storedEdges) →
                SourcePruningEnumerationNativeOrdinary.Ranges checkEmpty uv edgesOf reached after queries →
                ∃ (R N P H K : Nat) (entered : Cached)
                  (processed : List (SourcePruningEnumerationSelectedEdge.Result width))
                  (lastCaller : Caller width) (saved : Queries) (last : Memos) (next : Inventory)
                  (outcome : SourcePruningEnumerationNativeBranches.Result width),
                  (∀ er en ep eh ek,
                    run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
                      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel
                      (R + er) (N + en) (P + ep) (H + eh) (K + ek) uv caller before memos.query =
                      .narrowed checked prepared reached queries action candidate right
                        (some ([.ok ((uv, newHandle, scs, .node parentEntry storedEdges depth free), entered.core)],
                          some outcome))) ∧
                  Post formulas solver next caller lastCaller last ∧ last.query = saved ∧
                  (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Admitted uv receipt) ∧
                  (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.Pending receipt) ∧
                  (∀ receipt ∈ processed,
                    ∃ (reached : Caller width) (savedQueries : Queries)
                      (receiptInventory : Inventory) (receiptMemos : Memos),
                      SourcePruningEnumerationNativeBranches.advance receipt = some (reached, savedQueries) ∧
                      Post formulas solver receiptInventory caller reached receiptMemos ∧
                      receiptMemos.query = savedQueries) ∧
                  (∀ receipt ∈ processed, SourcePruningEnumerationNativeBranchCompletion.FragmentHistory before.core receipt) ∧
                  (∀ receipt ∈ processed,
                    SourcePruningEnumerationReceiptCallback.Completes graph templates metadata uv before.core receipt) ∧
                  (outcome = .complete processed lastCaller saved ∨ outcome = .stopped processed (some .unhandled)) ∧
                  ((∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), arityAllows edge.children.length scs = true →
                    SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
                    outcome = .complete processed lastCaller saved))
