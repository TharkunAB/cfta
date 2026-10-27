import MicroCFTA.EnumerationFlatNativeIndex

/-!
# Completed native count observations across forest representations

A successful old count supplies its actual finite paths. No extra lookup
bound or cache invariant is needed to identify the corresponding flat count.
-/

namespace MicroCFTA.SourceFlatPruningCompletedIndex

open EnumerationFlatCached EnumerationFlatNativeIndex
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Every completed old count equals the direct-root fold at the same occurrences. -/
theorem count_eq (related : FlatUnionFind.Represents flat earlier)
    (fuel : Nat) (change : Int) (scs : List EnumerationState.Suspended)
    (waiting after : EnumerationWaitingIndex.Waiting)
    (completed : SourcePruningEnumerationNativeIndex.count fuel earlier change scs waiting = some after) :
    count flat change scs waiting = after := by
  induction scs generalizing waiting after with
  | nil => exact Option.some.inj completed
  | cons sc rest ih =>
      unfold SourcePruningEnumerationNativeIndex.count at completed
      cases observed : SourceUnionFindRoot.root fuel earlier sc.var with
      | none =>
          simp only [observed, Option.bind_none] at completed
          cases completed
      | some root =>
          obtain ⟨size, reached⟩ := SourceUnionFindRoot.root_correct fuel earlier sc.var root observed
          have same : FlatUnionFind.root flat sc.var = root :=
            (UnionFind.reaches_unique (related sc.var) reached).1
          simp only [observed, Option.bind_some] at completed
          have tail := ih _ _ completed
          simpa only [count, EnumerationCanonicalWaiting.count, List.map_cons,
            EnumerationWaitingIndex.count, List.foldl_cons, same] using tail

/-- An actual completed old native write returns the related flat cache immediately. -/
theorem write_related (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (value : EnumerationState.UVarValue Symbol)
    (gained lost : List EnumerationState.Suspended)
    (completed : SourcePruningEnumerationNativeIndex.write heap fuel target value gained lost earlier = some after) :
    ∃ next, write heap target value gained lost flat = some next ∧ Related next after := by
  unfold SourcePruningEnumerationNativeIndex.write at completed
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none =>
      simp only [classified, Option.bind_none] at completed
      cases completed
  | some flag =>
      simp only [classified, Option.bind_some] at completed
      cases removed : SourcePruningEnumerationNativeIndex.count fuel earlier.core.representatives
          (-1) lost earlier.waiting with
      | none =>
          simp only [removed, Option.bind_none] at completed
          cases completed
      | some removedWaiting =>
          simp only [removed, Option.bind_some] at completed
          cases saved : SourcePruningEnumerationNativeIndex.count fuel earlier.core.representatives
              1 gained removedWaiting with
          | none =>
              simp only [saved, Option.bind_none] at completed
              cases completed
          | some savedWaiting =>
              simp only [saved, Option.bind_some, Option.some.injEq] at completed
              subst after
              have lostSame := count_eq related.core.representatives fuel (-1) lost _ _ removed
              have gainedSame := count_eq related.core.representatives fuel 1 gained _ _ saved
              let next := {flat with
                core := {flat.core with values := flat.core.values.set target value}
                expandable := fun other => if other = target then flag else flat.expandable other
                waiting := count flat.core.representatives 1 gained
                  (count flat.core.representatives (-1) lost flat.waiting)}
              refine ⟨next, ?_, ?_⟩
              · simp only [write, classified, Option.map_some]
                rfl
              change Related _ _
              refine ⟨?_, ?_, ?_⟩
              · exact ⟨related.core.valid, related.core.representatives, related.core.counter,
                  congrArg (fun values => values.set target value) related.core.values,
                  related.core.obligations, related.core.recursionAncestry, related.core.expansionAncestry⟩
              · change (fun other => if other = target then flag else flat.expandable other) =
                  (fun other => if other = target then flag else earlier.expandable other)
                rw [related.expandable]
              · change count flat.core.representatives 1 gained
                  (count flat.core.representatives (-1) lost flat.waiting) = savedWaiting
                rw [related.waiting, lostSame, gainedSame]

end MicroCFTA.SourceFlatPruningCompletedIndex
