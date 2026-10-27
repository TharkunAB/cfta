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

/-- Every actual ordinary output retains the entry and the literal hook invocation that emitted it. -/
theorem ordinary_output_invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (result : FoldResult Output Reason width)
    (observed : (SourcePruningEnumerationNativeOrdinaryContinuations.run hook checkEmpty r n p h k uv
      edgesOf caller before queries).2 = some result) :
    ∀ output ∈ foldOutputs result,
      ∃ fragment reached saved after,
        OrdinaryInvocation hook checkEmpty r n p h k uv edgesOf caller before queries fragment reached saved after ∧
        output ∈ hookOutputs (hook fragment reached saved after) := by
