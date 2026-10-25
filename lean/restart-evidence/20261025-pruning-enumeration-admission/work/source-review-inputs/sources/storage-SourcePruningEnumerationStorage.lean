import MicroCFTA.SourcePruningEnumerationOrdinaryBranches
import MicroCFTA.EnumerationSchedule

namespace MicroCFTA.SourcePruningEnumerationStorage
open EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

local instance storageMonadList : Monad List := {
  pure := fun value => [value],
  bind := fun values continuation => values.flatMap continuation
}

/-- An actual prepared child preserves storage and returns an allocated fragment. -/
theorem child_storage
    (scs : List EnumerationState.Suspended)
    (value : InternedConstructorTemplates.Value Symbol Constraint)
    (action : EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
    (before after : EnumerationState.State Symbol Constraint)
    (fragment : Fragments.Fragment Symbol)
    (storage : StorageValid before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild
      (EnumGuard := Constraint) scs value = some action)
    (observed : Success action before fragment after) :
    StorageValid after ∧ FragmentBound after.counter fragment ∧ before.counter ≤ after.counter := by
  cases value with
  | empty =>
    simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at prepared
    subst action
    exact (EnumerationSchedule.reject_unsuccessful before after fragment observed).elim
  | reference _name =>
    simp [SourcePruningEnumerationShallowChild.prepareChild] at prepared
  | node entry _edges _depth _free =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have nodeShape : fragment = .hole before.counter ∧
      after = {allocated (some (entry.identity + 1)) before with
        values := (allocated (some (entry.identity + 1)) before).values.set before.counter
          (.unenumerated (some (entry.identity + 1)) scs)} := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [setValue, bind, pure, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.bind, StateT.pure, StateT.modifyGet, ExceptT.bind, ExceptT.pure,
        ExceptT.bindCont, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := nodeShape
    refine ⟨set_storage _ (allocation_storage _ before storage) before.counter
      (.unenumerated (some (entry.identity + 1)) scs) ?_, Nat.lt_succ_self _, Nat.le_succ _⟩
    exact fun sc member => Nat.lt_trans (bounded sc member) (Nat.lt_succ_self _)
  | union entry _members _depth _free =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have unionShape : fragment = .hole before.counter ∧
      after = allocated (some (entry.identity + 1)) before := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := unionShape
    exact ⟨allocation_storage _ before storage, Nat.lt_succ_self _, Nat.le_succ _⟩
  | mu entry _body _depthShape _ordinaryShape =>
    by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
    · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at prepared
    simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true,
      ↓reduceIte, SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at prepared
    subst action
    have muShape : fragment = .hole before.counter ∧
      after = allocated (some (entry.identity + 1)) before := by
      unfold Success at observed
      rw [bind_single _ _ before (allocated (some (entry.identity + 1)) before)
        before.counter (allocate_exact _ _)] at observed
      simpa [pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run, eq_comm] using observed
    obtain ⟨rfl, rfl⟩ := muShape
    exact ⟨allocation_storage _ before storage, Nat.lt_succ_self _, Nat.le_succ _⟩

/-- The actual captured child list preserves storage through its completed prefix. -/
theorem staged_storage
    (inputs : List (InternedConstructorTemplates.Value Symbol Constraint ×
      List EnumerationState.Suspended))
    (before after : EnumerationState.State Symbol Constraint)
    (result : Option (List (Fragments.Fragment Symbol)))
    (storage : StorageValid before)
    (bounded : ∀ input ∈ inputs, ∀ sc ∈ input.2, sc.var < before.counter)
    (observed : Success (SourcePruningEnumerationEdgeTraversal.runStaged
      (inputs.map (fun input =>
        (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) input.2 input.1)))) before result after) :
    StorageValid after ∧
      (match result with | none => True | some fragments => FragmentsBound after.counter fragments) ∧
      before.counter ≤ after.counter := by
  induction inputs generalizing before after result with
  | nil =>
    obtain ⟨resultSame, afterSame⟩ := (success_pure (some []) result before after).mp observed
    subst result
    subst after
    exact ⟨storage, trivial, Nat.le_refl _⟩
  | cons input rest ih =>
    obtain ⟨value, bucket⟩ := input
    cases preparedChild : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) bucket value with
    | none =>
      simp only [List.map_cons, preparedChild, SourcePruningEnumerationEdgeTraversal.runStaged] at observed
      obtain ⟨resultSame, afterSame⟩ := (success_pure none result before after).mp observed
      subst result
      subst after
      exact ⟨storage, trivial, Nat.le_refl _⟩
    | some childAction =>
      simp only [List.map_cons, preparedChild, SourcePruningEnumerationEdgeTraversal.runStaged] at observed
      obtain ⟨fragment, middle, headSuccess, tailBindSuccess⟩ := (success_bind _ _ _ _ _).mp observed
      obtain ⟨tailResult, last, tailSuccess, mappedSuccess⟩ := (success_bind _ _ _ _ _).mp tailBindSuccess
      obtain ⟨resultSame, afterSame⟩ := (success_pure _ _ _ _).mp mappedSuccess
      subst last
      subst result
      obtain ⟨middleStorage, fragmentBound, middleGrows⟩ :=
        child_storage bucket value childAction before middle fragment storage
          (fun sc member => bounded (value, bucket) (List.mem_cons.mpr (.inl rfl)) sc member)
          preparedChild headSuccess
      obtain ⟨afterStorage, tailBounds, afterGrows⟩ := ih middle after tailResult middleStorage
        (fun input member sc scMember => Nat.lt_of_lt_of_le
          (bounded input (List.mem_cons.mpr (.inr member)) sc scMember) middleGrows) tailSuccess
      refine ⟨afterStorage, ?_, Nat.le_trans middleGrows afterGrows⟩
      cases tailResult with
      | none => trivial
      | some fragments =>
        exact ⟨fragmentBound_mono middle.counter after.counter afterGrows fragment fragmentBound, tailBounds⟩

/-- An actual prepared edge preserves storage and bounds its returned fragment. -/
theorem edge_storage
    (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
    (before after : EnumerationState.State Symbol Constraint)
    (result : Option (Fragments.Fragment Symbol))
    (storage : StorageValid before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (prepared : SourcePruningEnumerationEdgeTraversal.prepare scs edge = some action)
    (observed : Success action before result after) :
    StorageValid after ∧
      (match result with | none => True | some fragment => FragmentBound after.counter fragment) ∧
      before.counter ≤ after.counter := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
      simp [SourcePruningEnumerationEdgeTraversal.prepare,
        SourcePruningEnumerationEdgePrefix.prepare, allowed, projected] at prepared
    | some pair =>
      obtain ⟨tries, residual⟩ := pair
      simp only [SourcePruningEnumerationEdgeTraversal.prepare,
        SourcePruningEnumerationEdgePrefix.prepare, allowed, ↓reduceIte,
        projected, Option.some.injEq] at prepared
      subst action
      let inputs : List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended) :=
        edge.children.zipIdx.map (fun indexed =>
          (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries)))
      have stagedSame : inputs.map (fun input =>
        (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) input.2 input.1)) =
        edge.children.zipIdx.map (fun indexed =>
          (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries),
            SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
              (descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries)) indexed.1)) := by
        simp only [inputs, List.map_map]
        rfl
      have prefixExact : (tries.mapM suspend >>= fun own =>
        pure (edge.entry.key.symbol,
          edge.children.zipIdx.map (fun indexed =>
            (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
              SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1)), residual)) before =
        [.ok ((edge.entry.key.symbol,
          edge.children.zipIdx.map (fun indexed =>
            (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries),
              SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                (descendScs indexed.2 scs ++ descendScs indexed.2 (suspendedVars before.counter tries)) indexed.1)), residual),
          suspendedState tries.length before)] := by
        rw [bind_single _ _ _ _ _ (suspendMany_exact tries before)]
        rfl
      unfold Success at observed
      rw [bind_single _ _ _ _ _ prefixExact] at observed
      rw [← stagedSame] at observed
      dsimp only at observed
      obtain ⟨childrenResult, childrenAfter, childrenSuccess, continued⟩ :=
        (success_bind _ _ (suspendedState tries.length before) result after).mp observed
      obtain ⟨childrenStorage, childrenBounds, childrenGrows⟩ :=
        staged_storage inputs (suspendedState tries.length before) childrenAfter childrenResult
          (suspension_storage tries.length before storage) (by
            intro input member
            dsimp only [inputs] at member
            obtain ⟨indexed, _indexedMember, rfl⟩ := List.mem_map.mp member
            intro sc scMember
            rw [EnumerationSchedule.suspended_counter]
            rcases List.mem_append.mp scMember with inherited | ownMember
            · exact Nat.lt_of_lt_of_le
                (EnumerationSchedule.descend_bounded before.counter indexed.2 scs bounded sc inherited)
                (Nat.le_add_right _ _)
            · exact EnumerationSchedule.descend_bounded (before.counter + tries.length) indexed.2
                (suspendedVars before.counter tries)
                (EnumerationSchedule.suspended_bounded before.counter tries) sc ownMember)
          childrenSuccess
      cases childrenResult with
      | none =>
        obtain ⟨resultSame, afterSame⟩ := (success_pure none result childrenAfter after).mp continued
        subst result
        subst after
        refine ⟨childrenStorage, trivial, Nat.le_trans ?_ childrenGrows⟩
        rw [EnumerationSchedule.suspended_counter]
        exact Nat.le_add_right _ _
      | some fragments =>
        have returned : result = some (.node edge.entry.key.symbol fragments) ∧
          after = (match residual with
            | none => childrenAfter
            | some guard => {childrenAfter with obligations :=
                (guard, .node edge.entry.key.symbol fragments) :: childrenAfter.obligations}) := by
          cases residual <;>
            simpa [EnumerationSchedule.recordResidual, Success, bind, pure,
              modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.bind,
              StateT.pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk,
              ExceptT.run, eq_comm] using continued
        obtain ⟨rfl, rfl⟩ := returned
        cases residual with
        | none =>
          refine ⟨childrenStorage, childrenBounds, Nat.le_trans ?_ childrenGrows⟩
          rw [EnumerationSchedule.suspended_counter]
          exact Nat.le_add_right _ _
        | some guard =>
          refine ⟨guard_storage childrenAfter childrenStorage guard
            (.node edge.entry.key.symbol fragments) childrenBounds, childrenBounds,
            Nat.le_trans ?_ childrenGrows⟩
          rw [EnumerationSchedule.suspended_counter]
          exact Nat.le_add_right _ _
  · simp only [SourcePruningEnumerationEdgeTraversal.prepare,
      SourcePruningEnumerationEdgePrefix.prepare, allowed, Bool.false_eq_true,
      ↓reduceIte, Option.some.injEq] at prepared
    subst action
    simp [Success, reject, bind, StateT.bind, ExceptT.bind, ExceptT.mk, ExceptT.run] at observed

/-- Derive storage and fragment admission for the complete ordered ordinary branch stream. -/
theorem complete
    (scs : List EnumerationState.Suspended)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (InternedConstructorTemplates.EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (parentAvailable : InternedProbeProvenance.Available heap (.node entry storedEdges depth free))
    (parentClosed : free = [])
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (before : EnumerationState.State Symbol Constraint)
    (realized : SourcePruningEnumerationObservation.PendingRealized heap before)
    (storage : StorageValid before)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter) :
    ∃ branchRows : List (List (Except EnumerationState.Error
        (Option (Option (Fragments.Fragment Symbol)) × EnumerationState.State Symbol Constraint))),
      Language.All₂ (fun edge rows =>
        if arityAllows edge.children.length scs then
          match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
          | none => rows = [.ok (none, before)]
          | some _ =>
              ∃ (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
                (result : Option (Fragments.Fragment Symbol))
                (after : EnumerationState.State Symbol Constraint),
                SourcePruningEnumerationEdgeTraversal.prepare scs edge = some action ∧
                Success action before result after ∧ rows = [.ok (some result, after)] ∧
                after.counter = after.values.length ∧
                SourcePruningEnumerationObservation.PendingRealized heap after ∧
                StorageValid after ∧
                (∀ (fragment : Fragments.Fragment Symbol),
                  result = some fragment → FragmentBound after.counter fragment) ∧
                before.counter ≤ after.counter
        else rows = []) selectedEdges branchRows ∧
      SourcePruningEnumerationOrdinaryBranches.run scs selectedEdges before = branchRows.flatten := by
  obtain ⟨branchRows, related, raw⟩ := SourcePruningEnumerationOrdinaryBranches.run_complete
    scs heap entry storedEdges selectedEdges depth free ready parentAvailable parentClosed
    selected before realized storage.aligned
  refine ⟨branchRows, Language.All₂.imp ?_ related, raw⟩
  intro edge rows row
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [allowed, ↓reduceIte] at row ⊢
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
      simpa only [projected] using row
    | some _pair =>
      simp only [projected] at row ⊢
      obtain ⟨action, result, after, prepared, observed, rawRow, aligned, realized⟩ := row
      obtain ⟨afterStorage, resultBound, grows⟩ :=
        edge_storage scs edge action before after result storage bounded prepared observed
      refine ⟨action, result, after, prepared, observed, rawRow, aligned, realized,
        afterStorage, ?_, grows⟩
      intro fragment same
      subst result
      exact resultBound
  · simpa only [allowed, Bool.false_eq_true, ↓reduceIte] using row

end MicroCFTA.SourcePruningEnumerationStorage
