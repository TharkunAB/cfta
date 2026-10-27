
/-- An actual ordinary scan supplies its inherited nonterminal gate. -/
theorem ordinary_nonterminal
    (checkEmpty : Bool) (r n p h k uv target handle : Nat) (scs : List Suspended)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (entered : Core)
    (result : SourcePruningEnumerationNativeBranches.Result width)
    (observed : SourcePruningEnumerationNativeOrdinary.run checkEmpty r n p h k uv
      edgesOf caller before queries =
      ([.ok ((target, handle, scs, .node entry edges depth free), entered)], some result)) :
    scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
  have actualEntry := congrArg Prod.fst observed
  change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) =
    [.ok ((target, handle, scs, .node entry edges depth free), entered)] at actualEntry
  cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
  | false => rfl
  | true =>
      have actualScan := congrArg Prod.snd observed
      simp only [SourcePruningEnumerationNativeOrdinary.run, actualEntry, terminal,
