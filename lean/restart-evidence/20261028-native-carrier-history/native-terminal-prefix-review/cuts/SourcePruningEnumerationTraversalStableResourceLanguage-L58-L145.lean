variable {bits : Nat}

/-- Original resources and actual stable completion retain exactly the effective child restrictions. -/
theorem stable_complete_semantics_resources
    (seed : SourcePruningEnumerationIncomingReservation.Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (inputs : List (Node × List Suspended))
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available beforeCaller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 beforeCaller.checked)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed (cost inputs))
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      beforeCaller.checked.native.machine.heap)
    {r n p h k : Nat} {fragments : List Fragment} {afterCaller : Caller (bits + 2)}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
      SourcePruningEnumerationChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
        P H (k + extraIndex) inputs beforeCaller before memos.query =
        .complete fragments afterCaller savedQueries after) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning assignment after.core ↔
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core ∧
      All₂ (fun input fragment =>
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient input.1 (Fragments.fill assignment fragment) ∧
        ∀ sc ∈ (match input.1 with
          | .node _ _ _ _ => input.2
          | _ => if input.2.any (fun sc => EqualityTrie.isTerminal sc.trie) then input.2 else []),
          Suspended.Holds assignment (Fragments.fill assignment fragment) sc) inputs fragments := by
  induction inputs generalizing seed inventory beforeCaller before roots memos
      r n p h k fragments afterCaller after savedQueries with
  | nil =>
      have actual := observed 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
      simp only [SourcePruningEnumerationChildTraversal.run,
        SourcePruningEnumerationChildTraversal.Result.complete.injEq] at actual
      obtain ⟨rfl, rfl, rfl, rfl⟩ := actual
      intro ambient residualMeaning assignment
      constructor
      · intro satisfied
        exact ⟨satisfied, .nil⟩
      · rintro ⟨satisfied, _related⟩
        exact satisfied
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      obtain ⟨available, closed, bounded, pending⟩ := genuine incoming bucket (by simp)
      have headReservation : SourcePruningEnumerationIncomingReservation.Reserved bits seed (bucket.length + 1) :=
        reserved.prefix (by change bucket.length + 1 ≤ bucket.length + 1 + cost rest; omega)
      have headRanges := SourcePruningEnumerationChildCompletion.initial_ranges seed formulas solver inventory
        beforeCaller before checkEmpty bucket incoming roots memos initial safe paths counts bounded pending
        realized available closed fits headReservation known
      obtain ⟨headR, headN, headP, headH, headK, raw, middleCaller, middle,
        middleQueries, middleMemos, middleInventory, middleRoots, outer, waiting,
        headRun, headPost, headQueries, growth, middlePaths, _middleStorage,
        middleRealized, middleCounts, middleFlags, headOrigin, headProtected,
        _headReferences, _headPending, shape, middleFits, middleKnown⟩ :=
        SourcePruningEnumerationChildCompletion.complete_with_fragments_resources seed formulas solver inventory
          beforeCaller before checkEmpty bucket incoming roots memos initial safe paths counts flags realized
          bounded pending available closed fits headReservation known
      rcases shape with rejected |
        ⟨fragment, singleton, middleSafe, _fragmentBound, _fragmentPending, _fragmentSeparate⟩
      · subst raw
        have headCommon : SourcePruningEnumerationChildDispatch.run checkEmpty (r + headR) (n + headN)
            (max p headP) (max h headH) (k + headK) bucket incoming beforeCaller before memos.query =
            ((.ok (some []), middleCaller, middleQueries, outer, waiting), some middle) := by
          simpa only [Nat.add_comm] using headRun r n (max p headP) (max h headH) k
            (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        have impossible := observed headR headN (max p headP) (max h headH) headK
          (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        rw [SourcePruningEnumerationChildTraversal.run, headCommon] at impossible
        cases impossible
      · have headCommon : ∀ er en P H ek, max p headP ≤ P → max h headH ≤ H →
            SourcePruningEnumerationChildDispatch.run checkEmpty ((r + headR) + er) ((n + headN) + en)
              P H ((k + headK) + ek) bucket incoming beforeCaller before memos.query =
