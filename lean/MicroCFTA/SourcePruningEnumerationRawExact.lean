import MicroCFTA.SourcePruningEnumerationEdgeTraversal

namespace MicroCFTA.SourcePruningEnumerationRawExact
open EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

local instance rawMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- The concrete captured child traversal has exactly the observed successful raw result. -/
theorem runStaged_exact
    (inputs : List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended))
    (before after : EnumerationState.State Symbol Constraint)
    (result : Option (List (Fragments.Fragment Symbol))) :
    let staged := inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
        (EnumGuard := Constraint) input.2 input.1))
    Success (SourcePruningEnumerationEdgeTraversal.runStaged staged) before result after →
      SourcePruningEnumerationEdgeTraversal.runStaged staged before = [.ok (result, after)] := by
  dsimp only
  have childExact : ∀ (bucket : List EnumerationState.Suspended)
    (value : InternedConstructorTemplates.Value Symbol Constraint)
    (childAction : EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
    (start finish : EnumerationState.State Symbol Constraint)
    (fragment : Fragments.Fragment Symbol),
    SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) bucket value = some childAction →
      Success childAction start fragment finish → childAction start = [.ok (fragment, finish)] := by
    intro bucket value childAction start finish fragment childPrepared childObserved
    cases value with
    | empty =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at childPrepared
      subst childAction
      simp [Success, reject, ExceptT.run] at childObserved
    | reference name =>
      simp [SourcePruningEnumerationShallowChild.prepareChild] at childPrepared
    | node | union | mu =>
      by_cases terminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [SourcePruningEnumerationShallowChild.prepareChild, terminal] at childPrepared
      · simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true, ↓reduceIte,
          SourcePruningEnumerationNodes.encodeNode, Option.some.injEq] at childPrepared
        subst childAction
        simp_all [Success, allocate, inheritAncestry, setValue, bind, get, getThe,
          MonadStateOf.get, set, pure, modify, modifyGet, MonadStateOf.modifyGet,
          StateT.pure, StateT.bind, StateT.get, StateT.set, StateT.modifyGet,
          ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
  induction inputs generalizing before after result with
  | nil =>
    intro observed
    obtain ⟨resultSame, afterSame⟩ := (success_pure (some []) result before after).mp observed
    subst result
    subst after
    rfl
  | cons input rest ih =>
    intro observed
    obtain ⟨value, bucket⟩ := input
    cases preparedChild : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) bucket value with
    | none =>
      simp only [List.map_cons, preparedChild, SourcePruningEnumerationEdgeTraversal.runStaged] at observed ⊢
      obtain ⟨resultSame, afterSame⟩ := (success_pure none result before after).mp observed
      subst result
      subst after
      rfl
    | some childAction =>
      simp only [List.map_cons, preparedChild, SourcePruningEnumerationEdgeTraversal.runStaged] at observed ⊢
      obtain ⟨fragment, middle, headSuccess, tailBindSuccess⟩ := (success_bind _ _ _ _ _).mp observed
      obtain ⟨tailResult, last, tailSuccess, mappedSuccess⟩ := (success_bind _ _ _ _ _).mp tailBindSuccess
      obtain ⟨resultSame, afterSame⟩ := (success_pure _ _ _ _).mp mappedSuccess
      subst last
      subst result
      have headExact : childAction before = [.ok (fragment, middle)] := by
        exact childExact bucket value childAction before middle fragment preparedChild headSuccess
      have tailExact : SourcePruningEnumerationEdgeTraversal.runStaged
        (rest.map (fun input => (input.1, input.2,
          SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))) middle =
        [.ok (tailResult, after)] := by
        exact ih middle after tailResult tailSuccess
      rw [bind_single _ _ _ _ _ headExact, bind_single _ _ _ _ _ tailExact]
      rfl

/-- A captured concrete edge action has exactly the observed successful raw result. -/
theorem prepare_exact
    (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
    (before after : EnumerationState.State Symbol Constraint)
    (result : Option (Fragments.Fragment Symbol))
    (prepared : SourcePruningEnumerationEdgeTraversal.prepare scs edge = some action)
    (observed : Success action before result after) :
    action before = [.ok (result, after)] := by
  by_cases allowed : arityAllows edge.children.length scs = true
  ·
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
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
      rw [bind_single _ _ _ _ _ prefixExact] at observed ⊢
      rw [← stagedSame] at observed ⊢
      dsimp only at observed ⊢
      obtain ⟨childrenResult, childrenAfter, childrenSuccess, continued⟩ :=
        (success_bind _ _ (suspendedState tries.length before) result after).mp observed
      rw [bind_single _ _ _ _ _
        (runStaged_exact inputs (suspendedState tries.length before) childrenAfter childrenResult childrenSuccess)]
      cases childrenResult with
      | none =>
        simp_all [Success, pure, StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run]
      | some fragments =>
        cases residual <;>
          simp_all [EnumerationSchedule.recordResidual, Success, bind, pure,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.bind,
            StateT.pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
  · simp only [SourcePruningEnumerationEdgeTraversal.prepare,
      SourcePruningEnumerationEdgePrefix.prepare, allowed, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at prepared
    subst action
    simp [Success, reject, bind, StateT.bind, ExceptT.bind, ExceptT.mk, ExceptT.run] at observed

end MicroCFTA.SourcePruningEnumerationRawExact
