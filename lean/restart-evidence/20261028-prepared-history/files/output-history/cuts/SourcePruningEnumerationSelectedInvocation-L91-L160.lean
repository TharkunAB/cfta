
/-- Every actual selected output retains its actual preparation and hook invocation. -/
theorem output_invocation
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (folded : Fold Output Reason width)
    (observed : (run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).2 =
      some folded) :
    ∀ output ∈ foldOutputs folded,
      ∃ fragment reached saved after,
        Invocation hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries
          fragment reached saved after ∧ output ∈ hookOutputs (hook fragment reached saved after) := by
  unfold run at observed
  generalize preparation : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
    prepared at observed
  obtain ⟨raw, native⟩ := prepared
  cases native with
  | none => cases observed
  | some native =>
      cases native with
      | failed fault heap => cases observed
      | done value heap =>
          cases raw with
          | nil => cases observed
          | cons row rest =>
              cases row with
              | error error => cases observed
              | ok row =>
                  cases rest with
                  | cons row rest => cases observed
                  | nil =>
                      obtain ⟨⟨target, handle, scs, decoded⟩, entered⟩ := row
                      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
                      · simp only [terminal, ↓reduceIte] at observed
                        have same := Option.some.inj observed
                        subst folded
                        intro output member
                        obtain ⟨fragment, reached, saved, after, actual, emitted⟩ :=
                          receipt_output_invocation hook _ output member
                        refine ⟨fragment, reached, saved, after,
                          ⟨target, handle, scs, decoded, value, heap, entered, preparation, ?_⟩, emitted⟩
                        simpa only [terminal, ↓reduceIte] using actual
                      · simp only [terminal, Bool.false_eq_true, ↓reduceIte] at observed
                        cases value with
                        | node entry edges depth free =>
                            have same := Option.some.inj observed
                            subst folded
                            intro output member
                            obtain ⟨fragment, reached, saved, after, actual, emitted⟩ :=
                              SourcePruningEnumerationHookInvocation.run_output_invocation
                                hook checkEmpty r n p h k target scs
                                (EnumerationExpandableIndex.frame entered before)
                                (edgesOf (.node entry edges depth free))
                                (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries output member
                            refine ⟨fragment, reached, saved, after,
                              ⟨target, handle, scs, decoded, .node entry edges depth free, heap, entered,
                                preparation, ?_⟩, emitted⟩
                            simpa only [terminal, Bool.false_eq_true, ↓reduceIte] using actual
                        | empty | mu _ _ _ _ | reference _ | union _ _ _ _ =>
                            have same := Option.some.inj observed
                            subst folded
                            intro output member
                            obtain ⟨fragment, reached, saved, after, actual, emitted⟩ :=
                              receipt_output_invocation hook _ output member
                            refine ⟨fragment, reached, saved, after,
                              ⟨target, handle, scs, decoded, _, heap, entered, preparation, ?_⟩, emitted⟩
                            simpa only [terminal, Bool.false_eq_true, ↓reduceIte] using actual

end MicroCFTA.SourcePruningEnumerationSelectedContinuations
