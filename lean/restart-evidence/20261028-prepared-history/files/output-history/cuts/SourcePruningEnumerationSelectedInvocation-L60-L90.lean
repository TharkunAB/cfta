
/-- A singleton receipt can emit an output only through its completed-fragment hook. -/
theorem receipt_output_invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (receipt : Option (Receipt width)) :
    ∀ output ∈ foldOutputs (SourcePruningEnumerationReceiptContinuation.run hook receipt),
      ∃ fragment reached saved after,
        receipt = some (.complete fragment reached saved after) ∧
          output ∈ hookOutputs (hook fragment reached saved after) := by
  cases receipt with
  | none => intro output member; cases member
  | some receipt =>
      cases receipt with
      | unhandled => intro output member; cases member
      | rejected caller queries after => intro output member; cases member
      | complete fragment caller queries after =>
          cases actual : hook fragment caller queries after <;> intro output member
          all_goals
            refine ⟨fragment, caller, queries, after, rfl, ?_⟩
            simpa only [SourcePruningEnumerationReceiptContinuation.run, actual, foldOutputs, hookOutputs] using member
      | stopped fragments observation candidate =>
          cases actual : SourcePruningEnumerationNativeBranches.advance (.stopped fragments observation candidate) with
          | none =>
              intro output member
              simp only [SourcePruningEnumerationReceiptContinuation.run, actual, foldOutputs, List.not_mem_nil] at member
          | some endpoint =>
              obtain ⟨caller, queries⟩ := endpoint
              intro output member
              simp only [SourcePruningEnumerationReceiptContinuation.run, actual, foldOutputs, List.not_mem_nil] at member

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
