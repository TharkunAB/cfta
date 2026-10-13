import MicroCFTA.EqualityNestedUnaryAncestorEdit

/-!
# Original-index completion of the actual unary ancestor edit

The proof retains node_complete's concrete result and returned cache.
The optional path worker has the same run by node_eq. Original-index
replay then supplies Stored and every updated endpoint representation.
The archived draft is unchanged and remains outside the checked modules.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorEdit
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityNestedUnarySchedule EqualityMergedTargetReadback
open EqualityNestedUnaryAncestor EqualityNestedUnaryAncestorState
noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Concrete unary editing retains every original endpoint in its actual returned cache. -/
theorem edit_complete (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (root target : Value (Fin symbols) ConstraintKey) (targetRows : Node initial)
    (targetShape : NodeShape parent leaf targetRows target) (targetNormal : Replayable target)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (stored : Stored tags values state root) (represented : Represents parent leaf state rows values)
    (targetAvailable : Available state target) :
    Complete (fun _ => MergedColdMerge.work (nodeWork target root)) state (fun after output =>
      ∃ next : ValuesAt symbols count, Stored tags next after output ∧
        Represents parent leaf after (EqualityFixedProjectionInvariant.edit (Join initial) rows targetRows) next) := by
  obtain ⟨edges, related, rootClosed⟩ := stored
  have storedAgain : Stored tags values state root := ⟨edges, related, rootClosed⟩
  have fields := stored_fields tags values state facts (fun index => (represented index).1) edges related
  have resident : Edges state edges := EnumerationSoundness.all₂_outputs _ _ _ (fields.imp (fun _ _ valid => valid.1))
  have origin : ∀ edge ∈ nodeEdges root, ∃ index, edge.children = [values index] := by
    intro edge member
    have original : edge ∈ edges := by
      have found : edge ∈ nodeEdges (run (makeNode edges) state).1 := by simpa only [rootClosed] using member
      rw [EqualityLeafProjectionPhysical.makeNode_edges edges state facts.coherent facts.linked resident] at found
      exact ((EqualityLeafProjectionPhysical.normalized_member state facts.coherent edges resident edge).mp found).1
    obtain ⟨index, _, valid⟩ := EqualityMergedTargetShape.related_member _ _ _ fields edge original
    exact ⟨index, valid.2.2.2⟩
  have physical : ∀ edge ∈ nodeEdges root, ∃ child, ∃ selected : Node initial,
      edge.children = [child] ∧ Replayable child ∧ NodeShape parent leaf selected child := by
    intro edge member
    obtain ⟨index, children⟩ := origin edge member
    exact ⟨values index, rows index, children, (represented index).2⟩
  have rootValid := stored_root tags values state facts (fun index => (represented index).1) root storedAgain
  have rootKind := EqualityNestedUnaryUnion.normal_ordinary root state facts rootValid.1 rootValid.2
  have ordinaryInputs : ∀ edge ∈ nodeEdges root, ∃ child, edge.children = [child] ∧ EqualityLeafProjectionUnion.OrdinaryRoot child := by
    intro edge member
    obtain ⟨index, children⟩ := origin edge member
    exact ⟨values index, children, EqualityNestedUnaryUnion.normal_ordinary _ state facts (represented index).1 (represented index).2.1⟩
  have complete := node_complete parent leaf targetRows root target targetShape targetNormal physical state facts prepared
    (fun edge member child found => rootValid.1.children child (by
      cases root <;> try contradiction
      exact List.mem_flatMap.mpr ⟨edge, member, found⟩)) targetAvailable
  obtain ⟨bound, output, after, done, extension, available⟩ := complete
  refine ⟨bound, output, after, done, extension, ?_⟩
  have exactWork : run (nodeWork target root) state = (output, after) := by
    have first := done bound (Nat.le_refl _)
    have components := MergedSourceComparison.Result.done.inj first
    exact Prod.ext components.1 components.2
  have sourceEq := node_eq target root rootKind ordinaryInputs state
  rw [exactWork] at sourceEq
  have original := edit_stored parent leaf rows tags values state facts root target storedAgain represented
  rw [sourceEq] at original
  obtain ⟨actual, same, nextStored, closed⟩ := original
  have equal : actual = output := (Option.some.inj same).symm
  subst actual
  refine ⟨editedValues target values after, nextStored, ?_⟩
  intro index
  have correct := EqualityNestedUnaryWorkFacts.meet_correct parent leaf (rows index) targetRows (values index) target
    (represented index).2.2 targetShape (represented index).2.1 targetNormal after extension.facts extension.prepared
    (extension.available _ (represented index).1) (extension.available target targetAvailable)
  rw [closed index] at correct
  exact correct.2

end MicroCFTA.EqualityNestedUnaryAncestorEdit
