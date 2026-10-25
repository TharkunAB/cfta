/-- Run the selected edge and record its residual after the children finish. -/
noncomputable def prepare
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat)
    (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    Option (List (Option (Fragments.Fragment Symbol) ×
      EnumerationExpandableIndex.Cached Symbol Constraint) ×
      EnumerationExpandableIndex.Cached Symbol Constraint) :=
  (SourcePruningEnumerationCachedOwn.prepare heap scs edge before).bind fun prefixes =>
    match prefixes with
    | [] => some ([], before)
    | [((symbol, staged, residual), middle)] =>
        (SourcePruningEnumerationCachedStages.run heap fuel
          (staged.map (fun stage => (stage.1, stage.2.1))) middle).bind fun result =>
          match result.1 with
          | [] => some ([], result.2)
          | [(none, last)] => some ([(none, last)], last)
          | [(some fragments, last)] =>
              let fragment : Fragments.Fragment Symbol :=
                .node symbol fragments
              let finished : EnumerationExpandableIndex.Cached Symbol Constraint :=
                EnumerationExpandableIndex.frame
                  {last.core with obligations :=
                    match residual with
                    | none => last.core.obligations
                    | some guard => (guard, fragment) :: last.core.obligations} last
              some ([(some fragment, finished)], finished)
          | _ => none
    | _ => none

/-- Derive the selected edge outcome, its exact raw rows and its cache invariants. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (InternedConstructorTemplates.EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (scs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (parentAvailable : InternedProbeProvenance.Available heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) :
    ∃ (fuel : Nat)
      (outcome : Option (List (Option (Fragments.Fragment Symbol) ×
        EnumerationExpandableIndex.Cached Symbol Constraint) ×
        EnumerationExpandableIndex.Cached Symbol Constraint)),
      (∀ (extra : Nat), prepare heap (fuel + extra) scs edge before = outcome) ∧
      (SourcePruningEnumerationEdgeTraversal.prepare scs edge = none ↔ outcome = none) ∧
      (∀ (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol))),
        SourcePruningEnumerationEdgeTraversal.prepare scs edge = some action →
        ∃ (rows : List (Option (Fragments.Fragment Symbol) ×
            EnumerationExpandableIndex.Cached Symbol Constraint))
          (after : EnumerationExpandableIndex.Cached Symbol Constraint),
          outcome = some (rows, after) ∧
          ExceptT.run (action before.core) = rows.map (fun row => .ok (row.1, row.2.core)) ∧
          before.core.counter ≤ after.core.counter ∧
          after.core.counter = after.core.values.length ∧
          after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
          StorageValid after.core ∧ PendingRealized heap after.core ∧
          EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
          (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
            ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
          (rows = [] ∨ ∃ result : Option (Fragments.Fragment Symbol),
            rows = [(result, after)] ∧
            (∀ (fragment : Fragments.Fragment Symbol), result = some fragment →
              FragmentBound («Symbol» := Symbol) after.core.counter fragment))) := by
