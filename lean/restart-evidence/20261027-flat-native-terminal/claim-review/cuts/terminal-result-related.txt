/-- Preserve native effects, moved counts, raw diagnostics and optional cache recovery. -/
def ResultRelated
    (flat : ((Except (PrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ FoldRaw)) (Option TerminalRaw)) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint × EnumerationWaitingIndex.Waiting) ×
      Option (EnumerationFlatCached.Cached Symbol Constraint))
    (earlier : ((Except (OldPrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ OldFoldRaw)) (Option OldTerminalRaw)) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint × EnumerationWaitingIndex.Waiting) ×
      Option (EnumerationExpandableIndex.Cached Symbol Constraint)) : Prop :=
  (flat.1.2.1 = earlier.1.2.1 ∧ flat.1.2.2.1 = earlier.1.2.2.1 ∧
    EnumerationFlatState.Related flat.1.2.2.2.1 earlier.1.2.2.2.1 ∧
    flat.1.2.2.2.2 = earlier.1.2.2.2.2 ∧
    match flat.1.1, earlier.1.1 with
    | .error (.inl first), .error (.inl second) =>
        EnumerationResultRelation.Results EnumerationFlatState.Related first second
    | .error (.inr (.inl first)), .error (.inr (.inl second)) => first = second
    | .error (.inr (.inr first)), .error (.inr (.inr second)) =>
        EnumerationResultRelation.Results EnumerationFlatState.Related first second
    | .ok none, .ok none => True
    | .ok (some first), .ok (some second) =>
        EnumerationResultRelation.Results EnumerationFlatState.Related first second
    | _, _ => False) ∧
    EnumerationFlatNativeIndex.WritesRelated flat.2 earlier.2
