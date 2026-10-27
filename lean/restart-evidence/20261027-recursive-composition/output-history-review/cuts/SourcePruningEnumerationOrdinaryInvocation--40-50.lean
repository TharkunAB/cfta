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
