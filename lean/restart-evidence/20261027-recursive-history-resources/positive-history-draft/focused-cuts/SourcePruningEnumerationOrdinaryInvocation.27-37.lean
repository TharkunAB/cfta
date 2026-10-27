def OrdinaryInvocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached) : Prop :=
  ∃ target handle scs entry rows depth free entered,
    ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) =
      [.ok ((target, handle, scs, .node entry rows depth free), entered)] ∧
    scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
    Invocation hook checkEmpty r n p h k target scs (EnumerationExpandableIndex.frame entered before)
      (edgesOf (.node entry rows depth free)) caller queries fragment reached saved after
