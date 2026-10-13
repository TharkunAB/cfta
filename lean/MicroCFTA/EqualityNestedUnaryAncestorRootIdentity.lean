import MicroCFTA.EqualityNestedUnaryAncestorRootStep

/-!
# The actual ancestor identity stop test

Closed original row requests determine each complete normalized ancestor.
If all indexed endpoint meanings are unchanged, both ancestors are unchanged.
A physical identity stop is an allocation-free fixed point by constructor
replay in the actual returned cache.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorRoot
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityNestedUnarySchedule EqualityMergedTargetReadback
open EqualityNestedUnaryAncestorState InternedFreshProbeKeys
noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- A fixed indexed request list determines its exact canonical ancestor record. -/
theorem stored_unique (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (state : State (Fin symbols) ConstraintKey) (first second : Value (Fin symbols) ConstraintKey)
    (left : Stored tags values state first) (right : Stored tags values state second) : first = second := by
  obtain ⟨firstEdges, firstRelated, firstClosed⟩ := left
  obtain ⟨secondEdges, secondRelated, secondClosed⟩ := right
  have leftRows := EnumerationCorrectness.all₂_map_eq
    (fun index => (run (makeEdge (tags index).1 (tags index).2 [values index]) state).1)
    _ firstEdges (firstRelated.imp (fun _ _ equal => (congrArg Prod.fst equal).symm))
  have rightRows := EnumerationCorrectness.all₂_map_eq
    (fun index => (run (makeEdge (tags index).1 (tags index).2 [values index]) state).1)
    _ secondEdges (secondRelated.imp (fun _ _ equal => (congrArg Prod.fst equal).symm))
  have same : firstEdges = secondEdges := leftRows.trans rightRows.symm
  rw [same, secondClosed] at firstClosed
  exact (Prod.mk.inj firstClosed).1.symm

/-- Equal generated endpoint predicates determine equal resident complete endpoint records. -/
theorem values_unique (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (first second : ValuesAt symbols count) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (left : Represents parent leaf state rows first) (right : Represents parent leaf state rows second) : first = second := by
  funext index
  apply resident_reference_injective state facts.coherent _ _ (left index).1.resident (right index).1.resident
  exact (EqualityNestedUnaryMeet.identity_iff parent leaf (rows index) (rows index) (first index) (second index)
    (left index).2.2 (right index).2.2 (left index).2.1 (right index).2.1
    state facts (left index).1 (right index).1).mpr rfl

/-- The full indexed row state determines both normalized actual ancestors. -/
theorem roots_unique (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (rows : Projected initial left right) (first second : Roots symbols)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (left : RepresentsRoots parent leaf tags rows state first)
    (right : RepresentsRoots parent leaf tags rows state second) : first = second := by
  obtain ⟨values, leftStored, rightStored, leftValid, rightValid⟩ := left
  obtain ⟨others, otherLeftStored, otherRightStored, otherLeftValid, otherRightValid⟩ := right
  have sameLeft := values_unique parent leaf rows.1 values.1 others.1 state facts leftValid otherLeftValid
  have sameRight := values_unique parent leaf rows.2 values.2 others.2 state facts rightValid otherRightValid
  rw [← sameLeft] at otherLeftStored
  rw [← sameRight] at otherRightStored
  exact Prod.ext (stored_unique tags.1 values.1 state first.1 second.1 leftStored otherLeftStored)
    (stored_unique tags.2 values.2 state first.2 second.2 rightStored otherRightStored)

/-- Original row replay derives actual ancestor availability at both forest positions. -/
theorem roots_available (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (rows : Projected initial left right) (roots : Roots symbols)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (represented : RepresentsRoots parent leaf tags rows state roots) :
    Available state roots.1 ∧ Available state roots.2 := by
  obtain ⟨values, first, second, leftValid, rightValid⟩ := represented
  exact ⟨(stored_root tags.1 values.1 state facts (fun index => (leftValid index).1) roots.1 first).1,
    (stored_root tags.2 values.2 state facts (fun index => (rightValid index).1) roots.2 second).1⟩

/-- The source forest stop test uses the two physical root references in order. -/
def Same (first second : Roots symbols) : Prop :=
  first.1.referenceOf = second.1.referenceOf ∧ first.2.referenceOf = second.2.referenceOf

/-- In a coherent cache the stop test compares complete resident roots. -/
theorem same_iff_equal (first second : Roots symbols) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (left : Available state first.1 ∧ Available state first.2)
    (right : Available state second.1 ∧ Available state second.2) : Same first second ↔ first = second := by
  constructor
  · intro same
    exact Prod.ext
      (resident_reference_injective state facts.coherent _ _ left.1.resident right.1.resident same.1)
      (resident_reference_injective state facts.coherent _ _ left.2.resident right.2.resident same.2)
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- Every changing ancestor pass also changes the finite indexed row state. -/
theorem changed_rows (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (rows : Projected initial left right) (roots next : Roots symbols)
    (state after : State (Fin symbols) ConstraintKey) (facts : Facts state) (extension : Extension state after)
    (represented : RepresentsRoots parent leaf tags rows state roots)
    (output : RepresentsRoots parent leaf tags (EqualityFixedProjectionTermination.step (Join initial) rows) after next)
    (changed : ¬Same next roots) : EqualityFixedProjectionTermination.step (Join initial) rows ≠ rows := by
  intro fixed
  rw [fixed] at output
  have original := roots_grows parent leaf tags rows roots state after facts extension represented
  have equal := roots_unique parent leaf tags rows next roots after extension.facts output original
  exact changed (equal ▸ And.intro rfl rfl)

/-- An unchanged actual root pass replays without allocation in its returned cache. -/
theorem unchanged_fixed (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (rows : Projected initial left right) (roots next : Roots symbols)
    (state after : State (Fin symbols) ConstraintKey) (facts : Facts state) (extension : Extension state after)
    (represented : RepresentsRoots parent leaf tags rows state roots)
    (output : RepresentsRoots parent leaf tags (EqualityFixedProjectionTermination.step (Join initial) rows) after next)
    (done : run (stepWork roots) state = (next, after)) (same : Same next roots) :
    run (stepWork next) after = (next, after) := by
  have previous := roots_grows parent leaf tags rows roots state after facts extension represented
  have equal := (same_iff_equal next roots after extension.facts
    (roots_available parent leaf tags _ next after extension.facts output)
    (roots_available parent leaf tags rows roots after extension.facts previous)).mp same
  have repeated := replay (stepWork roots) state after facts.coherent.valid (by rw [done]; exact grows_refl after)
  rw [done] at repeated
  simpa only [equal] using repeated

end MicroCFTA.EqualityNestedUnaryAncestorRoot
