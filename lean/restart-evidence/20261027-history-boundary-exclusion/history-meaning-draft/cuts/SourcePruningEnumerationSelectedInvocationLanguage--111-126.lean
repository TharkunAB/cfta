          ambient (.node parentEntry storedEdges depth free) (assignment target) ∧
        (∀ sc ∈ scs, Suspended.Holds assignment (assignment target) sc) ∧
        Fragments.fill assignment fragment = assignment target := by
  obtain ⟨metadataSame, _coreSame⟩ := narrowed_right_identity holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos
    checked prepared ordinaryCaller ordinaryMemos.query action narrowed updated rightCore valid actual
  have nonterminal := invocation.entry_nonterminal entry
  subst updated
  exact narrowed_receipt_sound holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory fuel uv caller before memos checked prepared ordinaryCaller ordinaryMemos narrowed
    action (some [.ok ((false, metadata), rightCore)]) packet canonical chosen valid actual
    entryFuel target entryHandle scs entryValue entered entry enteredPacket seed inherited
    headInventory headCaller headMemos edge headBound fragment reached saved after returnedInventory returnedMemos
    prefixPost receipt callbackFuel recorded callbackAfter recording nonterminal freshArity retained

end MicroCFTA.SourcePruningEnumerationSelectedStep
