import MicroCFTA.EqualityNestedUnaryAncestorState
import MicroCFTA.EqualityNestedUnaryWorkFacts

/-!
# Actual unary ancestor edit effects

The unary source path worker executes one nested intersection per row and
then the original complete ancestor edge request. These concrete requests
derive the returned cache facts used by original-index reconstruction.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorEdit
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityNestedUnarySchedule EqualityMergedTargetReadback
open EqualityNestedUnaryAncestor EqualityNestedUnaryAncestorState
open EqualityLeafProjectionWorkers (sequence)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Execute the sole unary endpoint request, then retain the ancestor's complete tag. -/
noncomputable def rowWork (target : Value (Fin symbols) ConstraintKey) (edge : EdgeValue (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (EdgeValue (Fin symbols) ConstraintKey) :=
  (EqualityNestedUnaryWork.meet (edge.children.headD .empty) target).bind fun child =>
    makeEdge edge.entry.key.symbol edge.entry.key.constraint [child]

/-- Edit actual canonical ancestor rows in source order before parent normalization. -/
noncomputable def nodeWork (target root : Value (Fin symbols) ConstraintKey) : Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  (sequence ((nodeEdges root).map (rowWork target))).bind makeNode

/-- Ordered unary row work is the exact optional source edge worker. -/
theorem rows_eq (target : Value (Fin symbols) ConstraintKey) (edges : List (EdgeValue (Fin symbols) ConstraintKey))
    (inputs : ∀ edge ∈ edges, ∃ child, edge.children = [child] ∧ EqualityLeafProjectionUnion.OrdinaryRoot child)
    (state : State (Fin symbols) ConstraintKey) :
    run (EqualityLeafProjectionWorkers.editEdges (fun target value => EqualityNestedUnaryWork.meet value target) [([0], target)] edges) state =
      (some (run (sequence (edges.map (rowWork target))) state).1, (run (sequence (edges.map (rowWork target))) state).2) := by
  induction edges generalizing state with
  | nil => rfl
  | cons edge rest ih =>
      obtain ⟨child, children, ordinary⟩ := inputs edge List.mem_cons_self
      have tail := ih (fun edge member => inputs edge (List.mem_cons_of_mem _ member))
      cases edge with
      | mk entry original =>
          change original = [child] at children
          subst original
          have descend : EqualityLeafProjectionSyntax.descendEdits [([0], target)] 0 = [([], target)] := by
            simp [EqualityLeafProjectionSyntax.descendEdits]
          simp only [EqualityLeafProjectionWorkers.editEdges, EqualityLeafProjectionWorkers.editChildren,
            EqualityLeafProjectionWorkers.bindOptional, run_bind, descend, endpoint_edit target child ordinary,
            run, List.map_cons, sequence, rowWork]
          rw [tail]
          rfl

/-- The actual unary source path edit has exactly the concrete finite constructor result. -/
theorem node_eq (target root : Value (Fin symbols) ConstraintKey)
    (ordinary : EqualityLeafProjectionUnion.OrdinaryRoot root)
    (inputs : ∀ edge ∈ nodeEdges root, ∃ child, edge.children = [child] ∧ EqualityLeafProjectionUnion.OrdinaryRoot child)
    (state : State (Fin symbols) ConstraintKey) :
    run (EqualityLeafProjectionWorkers.edit (fun target value => EqualityNestedUnaryWork.meet value target) [([0], target)] root) state =
      (some (run (nodeWork target root) state).1, (run (nodeWork target root) state).2) := by
  cases root with
  | empty => simp [EqualityLeafProjectionWorkers.edit_empty, nodeWork, nodeEdges, sequence,
      makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds, run_bind, run]
  | reference | union | mu => contradiction
  | node entry edges depth free =>
      have exactRows := rows_eq target edges inputs state
      simp only [EqualityLeafProjectionWorkers.edit, EqualityLeafProjectionSyntax.atRoot,
        List.find?_cons, List.isEmpty_cons, List.find?_nil, Option.map_none,
        EqualityLeafProjectionWorkers.bindOptional, run_bind, exactRows, nodeWork, nodeEdges, run]

/-- One actual unary row request preserves source facts and returns its resident complete edge. -/
theorem row_complete (parent leaf : Fin symbols) (sourceRows targetRows : Node initial)
    (edge : EdgeValue (Fin symbols) ConstraintKey) (child target : Value (Fin symbols) ConstraintKey)
    (children : edge.children = [child]) (sourceShape : NodeShape parent leaf sourceRows child)
    (targetShape : NodeShape parent leaf targetRows target) (sourceNormal : Replayable child) (targetNormal : Replayable target)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (sourceAvailable : Available state child) (targetAvailable : Available state target) :
    Complete (fun _ => MergedColdMerge.work (rowWork target edge)) state EdgeResident := by
  have first := EqualityNestedUnaryWorkFacts.meet_correct parent leaf sourceRows targetRows child target
    sourceShape targetShape sourceNormal targetNormal state facts prepared sourceAvailable targetAvailable
  let result := run (EqualityNestedUnaryWork.meet child target) state
  have inputs : Values result.2 [result.1] := by
    intro value member
    simpa only [List.mem_singleton.mp member] using first.2.1
  have second := edge_verified edge.entry.key.symbol edge.entry.key.constraint [result.1] result.2 first.1.facts inputs
  let after := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint [result.1]) result.2
  have extension : Extension result.2 after.2 :=
    ⟨second.facts, first.1.prepared.preserve (by intro key entry body depth ordinary stored; exact stored), second.growth, second.history⟩
  refine ⟨0, after.1, after.2, ?_, first.1.trans extension, second.result _ _ rfl⟩
  intro _ _
  simp only [rowWork, children, List.headD_cons, MergedColdMerge.work, run_bind]
  rfl

/-- The actual unary parent edit derives complete cache facts from represented children. -/
theorem node_complete (parent leaf : Fin symbols) (targetRows : Node initial)
    (root target : Value (Fin symbols) ConstraintKey)
    (targetShape : NodeShape parent leaf targetRows target) (targetNormal : Replayable target)
    (inputs : ∀ edge ∈ nodeEdges root, ∃ child, ∃ rows : Node initial, edge.children = [child] ∧ Replayable child ∧ NodeShape parent leaf rows child)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (available : ∀ edge ∈ nodeEdges root, ∀ child ∈ edge.children, Available state child)
    (targetAvailable : Available state target) :
    Complete (fun _ => MergedColdMerge.work (nodeWork target root)) state Available := by
  let pre := fun state (edge : EdgeValue (Fin symbols) ConstraintKey) =>
    (∀ child ∈ edge.children, Available state child) ∧ Available state target
  have mapped := MergedColdMergeSoundness.map_related (fun _ edge => MergedColdMerge.work (rowWork target edge))
    pre (fun state (_ : EdgeValue (Fin symbols) ConstraintKey) edge => EdgeResident state edge)
    (fun _ _ extension edge valid => ⟨fun child member => extension.available child (valid.1 child member), extension.available target valid.2⟩)
    (fun before after extension _ edge valid => edge_grows before after extension.growth edge valid)
    (nodeEdges root) (fun edge member current facts prepared valid => by
      obtain ⟨child, rows, children, normal, shape⟩ := inputs edge member
      exact row_complete parent leaf rows targetRows edge child target children shape targetShape normal targetNormal
        current facts prepared (valid.1 child (by simp only [children, List.mem_singleton])) valid.2)
    state facts prepared (fun edge member => ⟨available edge member, targetAvailable⟩)
  have sequenceEq : MergedColdMerge.work (nodeWork target root) =
      MergedColdMerge.bind (MergedColdMerge.map (fun edge => MergedColdMerge.work (rowWork target edge)) (nodeEdges root))
        (fun edges => MergedColdMerge.work (makeNode edges)) := by
    funext current
    simp only [nodeWork, MergedColdMerge.bind, EqualityNestedUnaryWork.map_work,
      MergedColdMerge.work, run_bind, MergedSourceComparison.Result.bind]
  rw [sequenceEq]
  apply bind_complete _ _ state _ _ mapped
  intro edges after extension related
  have resident : Edges after edges := EnumerationSoundness.all₂_outputs _ _ _ related
  exact work_complete (makeNode edges) after extension.prepared Available
    (node_verified edges after extension.facts resident) (makeNode_noNewMu edges after)

end MicroCFTA.EqualityNestedUnaryAncestorEdit
