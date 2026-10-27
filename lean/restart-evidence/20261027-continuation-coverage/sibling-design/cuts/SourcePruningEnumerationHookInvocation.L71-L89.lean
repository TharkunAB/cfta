theorem run_output_invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    ∀ output ∈ foldOutputs (SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k
      target scs before edges caller queries),
      ∃ fragment reached saved after,
        Invocation hook checkEmpty r n p h k target scs before edges caller queries fragment reached saved after ∧
        output ∈ hookOutputs (hook fragment reached saved after) := by
  induction edges generalizing caller queries with
  | nil => intro output member; cases member
  | cons edge rest ih =>
      cases observed : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none =>
          intro output member
          simp only [SourcePruningEnumerationNativeContinuations.run, observed, foldOutputs, List.not_mem_nil] at member
      | some receipt =>
          cases receipt with
          | unhandled =>
