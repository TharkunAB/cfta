import MicroCFTA.EqualityNestedUnaryAncestorReplay

/-!
# Original endpoint indices in an actual ancestor cache

The representation retains each original complete edge request. Repeated
indices may replay the same physical row. The final parent request removes
duplicate rows and empty unary children through the actual constructor.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorState
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityNestedUnarySchedule
open EqualityNestedUnaryAncestor EqualityLeafProjectionWorkers EqualityLeafProjectionPhysical

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Every original index has a closed complete row request and the root has closed reconstruction. -/
def Stored (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (state : State (Fin symbols) ConstraintKey) (root : Value (Fin symbols) ConstraintKey) : Prop :=
  ∃ edges, Language.All₂ (fun index edge =>
    run (makeEdge (tags index).1 (tags index).2 [values index]) state = (edge, state)) (List.finRange count) edges ∧
    run (makeNode edges) state = (root, state)

/-- Closed original rows remain exact in a cache extension. -/
theorem stored_grows (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (before after : State (Fin symbols) ConstraintKey) (valid : Valid before) (growth : Grows before after)
    (root : Value (Fin symbols) ConstraintKey) (stored : Stored tags values before root) : Stored tags values after root := by
  obtain ⟨edges, related, parent⟩ := stored
  exact ⟨edges, related.imp (fun index edge closed => EqualityLeafProjectionClosedWorkers.work_grows _ before after valid edge closed growth),
    EqualityLeafProjectionClosedWorkers.work_grows _ before after valid root parent growth⟩

/-- Closed row requests derive every complete tag and original child position. -/
theorem stored_fields (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (available : ∀ index, Available state (values index))
    (edges : List (EdgeValue (Fin symbols) ConstraintKey))
    (related : Language.All₂ (fun index edge =>
      run (makeEdge (tags index).1 (tags index).2 [values index]) state = (edge, state)) (List.finRange count) edges) :
    Language.All₂ (fun index edge => EdgeResident state edge ∧ edge.entry.key.symbol = (tags index).1 ∧
      edge.entry.key.constraint = (tags index).2 ∧ edge.children = [values index]) (List.finRange count) edges := by
  apply related.imp
  intro index edge closed
  have inputs : Values state [values index] := by
    intro value member
    simpa only [List.mem_singleton.mp member] using available index
  have fields := MergedPhysicalGroupEdges.makeEdge_fields state facts (tags index).1 (tags index).2 [values index] inputs
  have resident := makeEdge_resident (tags index).1 (tags index).2 [values index] state facts.coherent
  rw [closed] at fields resident
  exact ⟨resident, fields⟩

/-- The source parent itself is an available replayable ordinary record. -/
theorem stored_root (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (available : ∀ index, Available state (values index))
    (root : Value (Fin symbols) ConstraintKey) (stored : Stored tags values state root) :
    Available state root ∧ EqualityMergedTargetReadback.Replayable root := by
  obtain ⟨edges, related, parent⟩ := stored
  have fields := stored_fields tags values state facts available edges related
  have resident : Edges state edges := EnumerationSoundness.all₂_outputs _ _ _ (fields.imp (fun _ _ valid => valid.1))
  have verified := node_verified edges state facts resident
  have normal := EqualityOrdinaryReadback.makeNode_normal edges state state facts.coherent facts.linked facts.coherent resident
    (by rw [parent]; exact grows_refl state)
  have output : Available state root := by simpa only [parent] using verified.result _ _ rfl
  exact ⟨output, state, facts, output, by simpa only [parent] using normal⟩

/-- Actual projection reads the represented original indices from the current ancestor root. -/
theorem project_complete (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (root : Value (Fin symbols) ConstraintKey) (stored : Stored tags values state root)
    (represented : Represents parent leaf state rows values) :
    Complete (fun _ => MergedColdMerge.work (makeUnion (projected root))) state (fun after result =>
      Available after result ∧ EqualityMergedTargetReadback.Replayable result ∧
        NodeShape parent leaf (EqualityFixedProjectionInvariant.project rows) result) := by
  obtain ⟨edges, related, rootClosed⟩ := stored
  have fields := stored_fields tags values state facts (fun index => (represented index).1) edges related
  have resident : Edges state edges := EnumerationSoundness.all₂_outputs _ _ _ (fields.imp (fun _ _ valid => valid.1))
  have complete := projected_complete parent leaf rows values edges (fields.imp (fun _ _ valid => valid.2.2.2))
    state state facts.coherent facts.linked resident facts prepared represented
  simpa only [rootClosed] using complete

/-- A pointwise output map preserves the original list positions. -/
theorem related_map (relation : Input → Output → Prop) (next : Input → Other → Prop)
    (change : Output → Other) (inputs : List Input) (outputs : List Output) (related : Language.All₂ relation inputs outputs)
    (holds : ∀ input output, relation input output → output ∈ outputs → next input (change output)) :
    Language.All₂ next inputs (outputs.map change) := by
  induction related with
  | nil => exact .nil
  | @cons first second rest tail head related ih =>
      exact .cons (holds first second head List.mem_cons_self)
        (ih (fun input output relation member => holds input output relation (List.mem_cons_of_mem _ member)))

/-- Read each original endpoint's completed nested intersection in one actual cache. -/
noncomputable def editedValues (target : Value (Fin symbols) ConstraintKey)
    (values : ValuesAt symbols count) (state : State (Fin symbols) ConstraintKey) : ValuesAt symbols count :=
  fun index => (run (EqualityNestedUnaryWork.meet (values index) target) state).1

/-- Every original endpoint request and ancestor constructor replays in the actual returned edit cache. -/
theorem edit_stored (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (root target : Value (Fin symbols) ConstraintKey) (stored : Stored tags values state root)
    (represented : Represents parent leaf state rows values) :
    let actual := run (edit (fun target value => EqualityNestedUnaryWork.meet value target) [([0], target)] root) state
    ∃ output, actual.1 = some output ∧ Stored tags (editedValues target values actual.2) actual.2 output ∧
      ∀ index, run (EqualityNestedUnaryWork.meet (values index) target) actual.2 =
        (editedValues target values actual.2 index, actual.2) := by
  obtain ⟨edges, related, rootClosed⟩ := stored
  have fields := stored_fields tags values state facts (fun index => (represented index).1) edges related
  have resident : Edges state edges := EnumerationSoundness.all₂_outputs _ _ _ (fields.imp (fun _ _ valid => valid.1))
  have origin : ∀ edge ∈ edges, ∃ index, edge.entry.key.symbol = (tags index).1 ∧
      edge.entry.key.constraint = (tags index).2 ∧ edge.children = [values index] := by
    intro edge member
    obtain ⟨index, _, valid⟩ := EqualityMergedTargetShape.related_member _ _ _ fields edge member
    exact ⟨index, valid.2⟩
  have unary : ∀ edge ∈ edges, edge.children.length = 1 := by
    intro edge member
    obtain ⟨index, _, _, children⟩ := origin edge member
    simp only [children, List.length_singleton]
  have ordinary : ∀ edge ∈ edges, ∀ child ∈ edge.children, EqualityLeafProjectionWorkers.Ordinary child := by
    intro edge member child found
    obtain ⟨index, _, _, children⟩ := origin edge member
    have same : child = values index := by simpa only [children, List.mem_singleton] using found
    rw [same]
    exact endpoint_ordinary parent leaf (rows index) (values index) state facts (represented index).1
      (represented index).2.1 (represented index).2.2
  let meet := fun (target value : Value (Fin symbols) ConstraintKey) => EqualityNestedUnaryWork.meet value target
  let edits := [([0], target)]
  let actual := run (edit meet edits root) state
  have rootKind (index : Fin count) := EqualityNestedUnaryUnion.normal_ordinary (values index) state facts
    (represented index).1 (represented index).2.1
  have original := EqualityNestedUnaryAncestorReplay.actual_original meet
    (fun target value => EqualityNestedUnaryWork.meet_safe value target) ([0], target) []
    (by simp [EqualityLeafProjectionSyntax.atRoot]) edges state state facts.coherent facts.linked facts.coherent
    (grows_refl state) resident unary ordinary
  simp only [rootClosed] at original
  obtain ⟨output, returned, parentClosed, source⟩ := original
  have childRead (index : Fin count) :
      editedChild meet edits actual.2 0 (values index) = editedValues target values actual.2 index := by
    simp only [editedChild, workerValue, edits]
    have descend : EqualityLeafProjectionSyntax.descendEdits [([0], target)] 0 = [([], target)] := by
      simp [EqualityLeafProjectionSyntax.descendEdits]
    rw [descend, endpoint_edit target (values index) (rootKind index) actual.2]
    rfl
  refine ⟨output, returned, ⟨edges.map (rebuild actual.2 (editedChild meet edits actual.2)), ?_, parentClosed⟩, ?_⟩
  · apply related_map _ _ _ _ _ fields
    intro index edge valid member
    have repeated := (source edge member).1
    change run (rebuildWork (editedChild meet edits actual.2) edge) actual.2 = _ at repeated
    simpa only [rebuildWork, valid.2.1, valid.2.2.1, valid.2.2.2,
      EqualityLeafProjectionSyntax.mapChildren, childRead] using repeated
  · intro index
    obtain ⟨edge, member, valid⟩ := related_input _ _ _ fields index (List.mem_finRange index)
    have childClosed := (source edge member).2 0 (values index) (by simp only [valid.2.2.2, indexed, List.mem_cons]; simp)
    have descend : EqualityLeafProjectionSyntax.descendEdits [([0], target)] 0 = [([], target)] := by
      simp [EqualityLeafProjectionSyntax.descendEdits]
    change run (edit meet (EqualityLeafProjectionSyntax.descendEdits edits 0) (values index)) actual.2 = _ at childClosed
    rw [show edits = [([0], target)] from rfl, descend, endpoint_edit target (values index) (rootKind index) actual.2] at childClosed
    exact Prod.ext rfl (Prod.mk.inj childClosed).2

end MicroCFTA.EqualityNestedUnaryAncestorState
