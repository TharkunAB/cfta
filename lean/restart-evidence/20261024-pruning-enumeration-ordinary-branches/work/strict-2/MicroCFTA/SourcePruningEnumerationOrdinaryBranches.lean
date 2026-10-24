import MicroCFTA.SourcePruningEnumerationRawExact

namespace MicroCFTA.SourcePruningEnumerationOrdinaryBranches
open EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

local instance ordinaryMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Run the stored edge branch body and keep the two unsupported stages distinct. -/
noncomputable def run (scs : List EnumerationState.Suspended)
    (selectedEdges : List (InternedConstructorTemplates.EdgeValue Symbol Constraint)) :
    EnumerateM Symbol Constraint (Option (Option (Fragments.Fragment Symbol))) :=
  choose selectedEdges >>= fun edge =>
    match SourcePruningEnumerationEdgeTraversal.prepare scs edge with
    | none => pure none
    | some action => action >>= fun result => pure (some result)

/-- Derive the complete ordered raw branch stream from the same available ordinary parent. -/
theorem run_complete
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
    (aligned : before.counter = before.values.length) :
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
                SourcePruningEnumerationObservation.PendingRealized heap after
        else rows = []) selectedEdges branchRows ∧
      run scs selectedEdges before = branchRows.flatten := by
  induction selectedEdges with
  | nil => exact ⟨[], .nil, rfl⟩
  | cons edge rest ih =>
    have selectedHead : edge ∈ storedEdges := by
      exact selected edge (List.mem_cons_self ..)
    have selectedTail : ∀ edge ∈ rest, edge ∈ storedEdges := by
      intro edge member
      exact selected edge (List.mem_cons_of_mem _ member)
    obtain ⟨tailRows, tailRelated, tailRaw⟩ := ih selectedTail
    have consRaw : ExceptT.run (run scs (edge :: rest) before) =
      ExceptT.run ((match SourcePruningEnumerationEdgeTraversal.prepare scs edge with
        | none => (pure none : EnumerateM Symbol Constraint (Option (Option (Fragments.Fragment Symbol))))
        | some action => action >>= fun result => pure (some result)) before) ++
      ExceptT.run (run scs rest before) := by
      simp only [run, run_bind, choose, ExceptT.run, List.map_cons, List.flatMap_cons]
    by_cases allowed : arityAllows edge.children.length scs = true
    ·
      cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
      | none =>
        refine ⟨[.ok (none, before)] :: tailRows, .cons ?_ tailRelated, ?_⟩
        · simp only [allowed, ↓reduceIte, projected]
        · change ExceptT.run (run scs (edge :: rest) before) = _
          rw [consRaw, tailRaw]
          simp only [SourcePruningEnumerationEdgeTraversal.prepare,
            SourcePruningEnumerationEdgePrefix.prepare, allowed, ↓reduceIte, projected]
          rfl
      | some pair =>
        obtain ⟨tries, residual⟩ := pair
        obtain ⟨action, childrenResult, childrenAfter, after, prepared, _childrenSuccess,
          _completedPrefixSuccess, _childrenShape, _afterShape, observed, _afterCounter,
          afterAligned, afterRealized⟩ := by
            simpa only [projected] using
              SourcePruningEnumerationEdgeTraversal.prepare_complete scs edge heap entry
                storedEdges depth free ready parentAvailable parentClosed selectedHead
                before realized aligned allowed
        have actionRaw : action before =
          [.ok (childrenResult.map (fun fragments => Fragments.Fragment.node edge.entry.key.symbol fragments), after)] := by
          exact SourcePruningEnumerationRawExact.prepare_exact scs edge action before after _ prepared observed
        refine ⟨[.ok (some (childrenResult.map (fun fragments =>
          Fragments.Fragment.node edge.entry.key.symbol fragments)), after)] :: tailRows,
          .cons ?_ tailRelated, ?_⟩
        · simp only [allowed, ↓reduceIte, projected]
          exact ⟨action, _, after, prepared, observed, rfl, afterAligned, afterRealized⟩
        · change ExceptT.run (run scs (edge :: rest) before) = _
          rw [consRaw, prepared]
          rw [bind_single _ _ before after _ actionRaw, tailRaw]
          rfl
    · refine ⟨[] :: tailRows, .cons ?_ tailRelated, ?_⟩
      · simp only [allowed, Bool.false_eq_true, ↓reduceIte]
      · change ExceptT.run (run scs (edge :: rest) before) = _
        rw [consRaw, tailRaw]
        simp only [SourcePruningEnumerationEdgeTraversal.prepare,
          SourcePruningEnumerationEdgePrefix.prepare, allowed, Bool.false_eq_true, ↓reduceIte]
        rfl

end MicroCFTA.SourcePruningEnumerationOrdinaryBranches
