import MicroCFTA.EqualityNestedUnaryAncestorEditCompletion
import MicroCFTA.EqualityNestedUnaryTermination
import MicroCFTA.InternedNormalizationFree

/-!
# Both actual unary ancestor edits in one returned cache

Both projections read the original roots before either edit starts.
The edits run in forest order. Each returned cache retains every original
row index and complete ancestor tag. No additional preparation cache is used.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorRoot
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityNestedUnarySchedule EqualityMergedTargetReadback
open EqualityNestedUnaryAncestor EqualityNestedUnaryAncestorState
noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Two ancestor roots retain the source forest positions. -/
abbrev Roots (symbols : Nat) := Value (Fin symbols) ConstraintKey × Value (Fin symbols) ConstraintKey

/-- Original complete row tags remain fixed throughout iteration. -/
abbrev Tags (symbols left right : Nat) :=
  (Fin left → Fin symbols × ConstraintKey) × (Fin right → Fin symbols × ConstraintKey)

/-- Original indexed endpoints represent both actual physical ancestor roots. -/
def RepresentsRoots (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (rows : Projected initial left right) (state : State (Fin symbols) ConstraintKey) (roots : Roots symbols) : Prop :=
  ∃ values : Physical symbols left right,
    Stored tags.1 values.1 state roots.1 ∧ Stored tags.2 values.2 state roots.2 ∧
      Represents parent leaf state rows.1 values.1 ∧ Represents parent leaf state rows.2 values.2

/-- Cache extension preserves the exact original ancestor requests and endpoint meanings. -/
theorem roots_grows (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (rows : Projected initial left right) (roots : Roots symbols)
    (before after : State (Fin symbols) ConstraintKey) (facts : Facts before) (extension : Extension before after)
    (represented : RepresentsRoots parent leaf tags rows before roots) :
    RepresentsRoots parent leaf tags rows after roots := by
  obtain ⟨values, first, second, leftValid, rightValid⟩ := represented
  exact ⟨values,
    stored_grows tags.1 values.1 before after facts.coherent.valid extension.growth roots.1 first,
    stored_grows tags.2 values.2 before after facts.coherent.valid extension.growth roots.2 second,
    represents_grows parent leaf before after extension rows.1 values.1 leftValid,
    represents_grows parent leaf before after extension rows.2 values.2 rightValid⟩

/-- Read both snapshot unions, then edit the first and second actual ancestor. -/
noncomputable def stepWork (roots : Roots symbols) : Work (Fin symbols) ConstraintKey (Roots symbols) :=
  (makeUnion (projected roots.1)).bind fun first =>
    (makeUnion (projected roots.2)).bind fun second =>
      (EqualityNestedUnaryAncestorEdit.nodeWork second roots.1).bind fun newLeft =>
        (EqualityNestedUnaryAncestorEdit.nodeWork first roots.2).bind fun newRight =>
          .pure (newLeft, newRight)

/-- Both ancestor edits derive the reciprocal indexed row pass in their actual returned cache. -/
theorem step_complete (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (rows : Projected initial left right) (roots : Roots symbols)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : RepresentsRoots parent leaf tags rows state roots) :
    Complete (fun _ => MergedColdMerge.work (stepWork roots)) state (fun after output =>
      RepresentsRoots parent leaf tags (EqualityFixedProjectionTermination.step (Join initial) rows) after output) := by
  obtain ⟨values, leftStored, rightStored, leftValid, rightValid⟩ := represented
  have work_bind {First Output : Type} (work : Work (Fin symbols) ConstraintKey First)
      (next : First → Work (Fin symbols) ConstraintKey Output) :
      MergedColdMerge.work (work.bind next) = MergedColdMerge.bind (MergedColdMerge.work work)
        (fun value => MergedColdMerge.work (next value)) := by
    funext current
    simp only [MergedColdMerge.work, MergedColdMerge.bind, run_bind, Result.bind]
  simp only [stepWork, work_bind]
  apply bind_complete _ _ state _ _
    (project_complete parent leaf rows.1 tags.1 values.1 state facts prepared roots.1 leftStored leftValid)
  intro first afterFirst firstExtension firstValid
  have firstFacts := firstExtension.facts
  have rightStoredFirst := stored_grows tags.2 values.2 state afterFirst facts.coherent.valid
    firstExtension.growth roots.2 rightStored
  have rightValidFirst := represents_grows parent leaf state afterFirst firstExtension rows.2 values.2 rightValid
  apply bind_complete _ _ afterFirst _ _
    (project_complete parent leaf rows.2 tags.2 values.2 afterFirst firstFacts firstExtension.prepared
      roots.2 rightStoredFirst rightValidFirst)
  intro second afterSecond secondExtension secondValid
  have both := firstExtension.trans secondExtension
  apply bind_complete _ _ afterSecond _ _
    (EqualityNestedUnaryAncestorEdit.edit_complete parent leaf rows.1 tags.1 values.1 roots.1 second _
      secondValid.2.2 secondValid.2.1 afterSecond secondExtension.facts secondExtension.prepared
      (stored_grows tags.1 values.1 state afterSecond facts.coherent.valid both.growth roots.1 leftStored)
      (represents_grows parent leaf state afterSecond both rows.1 values.1 leftValid) secondValid.1)
  intro newLeft afterLeft leftExtension editedLeft
  obtain ⟨nextLeft, nextLeftStored, nextLeftValid⟩ := editedLeft
  have previous := both.trans leftExtension
  apply bind_complete _ _ afterLeft _ _
    (EqualityNestedUnaryAncestorEdit.edit_complete parent leaf rows.2 tags.2 values.2 roots.2 first _
      firstValid.2.2 firstValid.2.1 afterLeft leftExtension.facts leftExtension.prepared
      (stored_grows tags.2 values.2 state afterLeft facts.coherent.valid previous.growth roots.2 rightStored)
      (represents_grows parent leaf state afterLeft previous rows.2 values.2 rightValid)
      ((secondExtension.trans leftExtension).available first firstValid.1))
  intro newRight afterRight rightExtension editedRight
  obtain ⟨nextRight, nextRightStored, nextRightValid⟩ := editedRight
  apply pure_complete (newLeft, newRight) afterRight rightExtension.facts rightExtension.prepared
  exact ⟨(nextLeft, nextRight),
    stored_grows tags.1 nextLeft afterLeft afterRight leftExtension.facts.coherent.valid rightExtension.growth
      newLeft nextLeftStored,
    nextRightStored,
    represents_grows parent leaf afterLeft afterRight rightExtension _ nextLeft nextLeftValid,
    nextRightValid⟩

/-- The exact work run supplies the state extension and both indexed ancestor representations. -/
theorem step_correct (parent leaf : Fin symbols) (tags : Tags symbols left right)
    (rows : Projected initial left right) (roots : Roots symbols)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : RepresentsRoots parent leaf tags rows state roots) :
    let actual := run (stepWork roots) state
    Extension state actual.2 ∧
      RepresentsRoots parent leaf tags (EqualityFixedProjectionTermination.step (Join initial) rows) actual.2 actual.1 := by
  obtain ⟨bound, value, after, done, extension, valid⟩ := step_complete parent leaf tags rows roots state facts prepared represented
  have components := Result.done.inj (done bound (Nat.le_refl _))
  dsimp only
  rw [components.1, components.2]
  exact ⟨extension, valid⟩

end MicroCFTA.EqualityNestedUnaryAncestorRoot
