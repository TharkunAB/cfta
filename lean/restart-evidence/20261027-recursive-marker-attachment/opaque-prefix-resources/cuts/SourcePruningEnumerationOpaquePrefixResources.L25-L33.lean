
/-- Ordered concatenation adds each original child reservation, including duplicates. -/
theorem cost_append (consumed remaining : List (Node × List Suspended)) :
    cost (consumed ++ remaining) = cost consumed + cost remaining := by
  induction consumed with
  | nil => simp only [List.nil_append, SourcePruningEnumerationTraversalCompletion.cost, Nat.zero_add]
  | cons input consumed ih =>
      rcases input with ⟨value, bucket⟩
      simp only [List.cons_append, SourcePruningEnumerationTraversalCompletion.cost, ih, Nat.add_assoc]
