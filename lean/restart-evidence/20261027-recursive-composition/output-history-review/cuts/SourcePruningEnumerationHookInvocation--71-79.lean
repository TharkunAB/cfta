theorem run_output_invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    ∀ output ∈ foldOutputs (SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
      target scs before edges caller queries),
      ∃ fragment reached saved after,
        Invocation hook checkEmpty r n p h k target scs before edges caller queries fragment reached saved after ∧
        output ∈ hookOutputs (hook fragment reached saved after) := by
