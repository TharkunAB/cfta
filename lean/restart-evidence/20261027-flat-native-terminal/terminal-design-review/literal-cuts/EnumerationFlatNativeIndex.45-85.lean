      fun other => if other = target then flag else before.expandable other,
      count before.core.representatives 1 gained
        (count before.core.representatives (-1) lost before.waiting)⟩

/-- Optional writes fail together or return related complete caches. -/
def WritesRelated (flat : Option (Cached Symbol EnumGuard))
    (earlier : Option (EnumerationExpandableIndex.Cached Symbol EnumGuard)) : Prop :=
  match flat, earlier with
  | none, none => True
  | some flat, some earlier => Related flat earlier
  | _, _ => False

/-- One shared sufficient bound preserves the actual native write and both indexes. -/
theorem write_stable (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (target : Nat) (value : EnumerationState.UVarValue Symbol)
    (gained lost : List EnumerationState.Suspended) :
    ∃ fuel, ∀ extra, WritesRelated (write heap target value gained lost flat)
      (SourcePruningEnumerationNativeIndex.write heap (fuel + extra) target value gained lost earlier) := by
  obtain ⟨lostFuel, lostRun⟩ := count_stable related.core.representatives lost
  obtain ⟨gainedFuel, gainedRun⟩ := count_stable related.core.representatives gained
  refine ⟨lostFuel + gainedFuel, ?_⟩
  intro extra
  have removed := lostRun (gainedFuel + extra) (-1) earlier.waiting
  have saved := gainedRun (lostFuel + extra) 1
    (count flat.core.representatives (-1) lost earlier.waiting)
  rw [← Nat.add_assoc] at removed
  have order : gainedFuel + (lostFuel + extra) = lostFuel + gainedFuel + extra := by omega
  rw [order] at saved
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none => simp [write, SourcePruningEnumerationNativeIndex.write, classified, WritesRelated]
  | some flag =>
      simp only [write, classified, Option.map_some,
        SourcePruningEnumerationNativeIndex.write, Option.bind_some, removed, saved]
      change Related _ _
      refine ⟨?_, ?_, ?_⟩
      · exact ⟨related.core.valid, related.core.representatives, related.core.counter,
          congrArg (fun values => values.set target value) related.core.values,
          related.core.obligations, related.core.recursionAncestry, related.core.expansionAncestry⟩
      · rw [related.expandable]
      · rw [related.waiting]
