/-- An opaque boundary preparation ignores the unused native-index fuel. -/
theorem opaque_prepare_fuel
    (heap : InternedConstructorTemplates.State Symbol Constraint) (firstFuel nextFuel : Nat)
    (bucket : List Suspended) (value : Node) (before : Cached)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    SourcePruningEnumerationCachedPrepare.prepareChild heap firstFuel bucket value before =
      SourcePruningEnumerationCachedPrepare.prepareChild heap nextFuel bucket value before := by
  cases value with
  | empty => simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  | reference name => simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  | node entry edges depth free =>
      simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true] at boundary
  | union entry members depth free | mu entry members depth free => rfl
