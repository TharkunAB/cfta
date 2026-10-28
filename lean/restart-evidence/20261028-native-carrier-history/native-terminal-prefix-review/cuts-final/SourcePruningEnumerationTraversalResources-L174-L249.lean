          (fun valid => tailPending (headPending valid)), ?_, ?_, finalFits, finalKnown⟩
        · intro er en P H ek largeP largeH
          have head := headRun (tailR + er) (tailN + en) P H (tailK + ek)
            (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
          have tail := tailRun (r + er) (n + en) P H (k + ek)
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
          have headExact : SourcePruningEnumerationChildDispatch.run checkEmpty ((r + tailR) + er)
              ((n + tailN) + en) P H ((k + tailK) + ek) bucket incoming beforeCaller before memos.query =
              ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle) := by
            simpa only [Nat.add_assoc, singleton] using head
          have tailExact : SourcePruningEnumerationChildTraversal.run checkEmpty ((r + tailR) + er)
              ((n + tailN) + en) P H ((k + tailK) + ek) rest middleCaller middle middleQueries = tailResult := by
            simpa only [headQueries, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
          simp only [SourcePruningEnumerationChildTraversal.run, headExact, tailExact, result]
          cases tailResult <;> rfl
        · intro held storedFragment stored
          have first := protects held storedFragment stored
          have middleStored : middle.core.values[held]? = some (.enumerated storedFragment) := first.value.trans stored
          exact first.trans (tailProtected held storedFragment middleStored)
        · intro held inside root avoids
          have first := headProtected held inside root (avoids incoming bucket (by simp))
          apply first.trans
          apply tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root
          intro value retained member
          exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member))
        · intro allowed valid allowedInputs
          apply tailReferences allowed
            (headReferences allowed valid (allowedInputs incoming bucket (by simp)))
          intro value retained member
          exact allowedInputs value retained (List.mem_cons_of_mem _ member)
        · intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact fragmentBound_mono _ _ tailGrowth _ fragmentBound
          · exact tailBounds child member
        · rcases tailShape with ⟨completed, afterSafe, fragmentHistory⟩ | ⟨outer, waiting, stopped⟩
          · subst tailResult
            refine .inl ⟨rfl, afterSafe, ?_⟩
            intro child member
            rcases List.mem_cons.mp member with rfl | member
            · refine ⟨pendingFragment_preserved middle.core after.core middleSafe afterSafe tailGrowth
                child fragmentBound fragmentPending tailOrigin tailProtected, ?_⟩
              intro held inside root avoids
              have first := headProtected held inside root (avoids incoming bucket (by simp))
              have last := tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root (by
                intro value retained member
                exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member)))
              exact (fragmentAvoid_classes middle.core.representatives after.core.representatives held child
                last.classes).mpr (fragmentSeparate held inside root (avoids incoming bucket (by simp)))
            · obtain ⟨childPending, childSeparate⟩ := fragmentHistory child member
              refine ⟨childPending, ?_⟩
              intro held inside root avoids
              have first := headProtected held inside root (avoids incoming bucket (by simp))
              apply childSeparate held (Nat.lt_of_lt_of_le inside growth) first.root
              intro value retained member
              exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member))
          · subst tailResult
            exact .inr ⟨outer, waiting, rfl⟩

/-- Original resources retain the full earlier traversal interface. -/
theorem complete_resources
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
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
