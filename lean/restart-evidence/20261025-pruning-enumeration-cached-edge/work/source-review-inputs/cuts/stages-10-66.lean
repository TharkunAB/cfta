/-- Run the actual prepared children and retain the completed-prefix cache. -/
def run
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat) :
    List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended) →
      EnumerationExpandableIndex.Cached Symbol Constraint →
      Option (List (Option (List (Fragments.Fragment Symbol)) ×
        EnumerationExpandableIndex.Cached Symbol Constraint) ×
        EnumerationExpandableIndex.Cached Symbol Constraint)
  | [], before => some ([(some [], before)], before)
  | (value, bucket) :: rest, before =>
      match SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) bucket value with
      | none => some ([(none, before)], before)
      | some _action =>
          (SourcePruningEnumerationCachedPrepare.prepareChild heap fuel bucket value before).bind fun rows =>
            match rows with
            | [] => some ([], before)
            | [(fragment, middle)] =>
                (run heap fuel rest middle).map fun result =>
                  (result.1.map (fun row =>
                    (row.1.map (fun fragments => fragment :: fragments), row.2)), result.2)
            | _ => none

/-- Derive stable cached execution and the exact existing raw child stream. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (inputs : List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended))
    (roots : Nat → Nat) (coherent : InternedRecordCoherence.Coherent heap) :
    ∀ (before : EnumerationExpandableIndex.Cached Symbol Constraint),
      StorageValid before.core → PendingRealized heap before.core →
      Roots before.core.representatives roots →
      EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting →
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) →
      (∀ input ∈ inputs, InternedProbeProvenance.Available heap input.1) →
      (∀ input ∈ inputs, input.1.free = []) →
      (∀ input ∈ inputs, ∀ sc ∈ input.2, sc.var < before.core.counter) →
      let staged := inputs.map (fun input =>
        (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) input.2 input.1))
      ∃ (fuel : Nat)
        (rows : List (Option (List (Fragments.Fragment Symbol)) ×
          EnumerationExpandableIndex.Cached Symbol Constraint))
        (after : EnumerationExpandableIndex.Cached Symbol Constraint),
        (∀ (extra : Nat), run heap (fuel + extra) inputs before = some (rows, after)) ∧
        ExceptT.run (SourcePruningEnumerationEdgeTraversal.runStaged staged before.core) =
          rows.map (fun row => .ok (row.1, row.2.core)) ∧
        before.core.counter ≤ after.core.counter ∧
        after.core.counter = after.core.values.length ∧
        after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
        StorageValid after.core ∧ PendingRealized heap after.core ∧
        EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
        (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
          ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
        (rows = [] ∨ ∃ result : Option (List (Fragments.Fragment Symbol)),
          rows = [(result, after)] ∧
          (∀ (fragments : List (Fragments.Fragment Symbol)), result = some fragments →
            FragmentsBound («Symbol» := Symbol) after.core.counter fragments)) := by
