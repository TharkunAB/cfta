import MicroCFTA.EqualityNestedUnaryTermination

/-!
# Constructive entry to the nested projected schedule

Actual source edge and node requests compile every selected generated row
set. The completed runtime cache supplies the representation invariant for
the bounded endpoint loop. No prepared replacement cache is inserted.
-/
namespace MicroCFTA.EqualityNestedUnaryCompile
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryChild EqualityNestedUnaryProduct EqualityMergedTargetReadback
open EqualityNestedUnaryMeet EqualityNestedUnarySchedule

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- A nullary constructor derives the exact complete child guard and its canonical readback. -/
theorem leaf_complete (symbol : Fin symbols) (row : Row initial)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state) :
    Complete (fun _ => MergedColdMerge.work (EqualityLeafProjectionNullary.build [(symbol, EqualityLeafProjectionLeafCache.constraint row)])) state
      (fun after result => Available after result ∧ Replayable result ∧ LeafRow symbol row result) := by
  let rows := [(symbol, EqualityLeafProjectionLeafCache.constraint row)]
  let computation := EqualityLeafProjectionNullary.build rows
  let result := run computation state
  have checked := EqualityLeafProjectionCompileAvailability.nullary_available rows state
    (⟨facts.coherent, facts.cached, facts.linked⟩ : EqualityLeafProjectionCompileAvailability.Facts state)
  have resultFacts : Facts result.2 := ⟨checked.1.coherent, checked.1.cached, checked.1.linked⟩
  have unchanged : NoNewMu state result.2 := by
    have first := sequence_noNewMu (EqualityLeafProjectionNullary.requests rows) (by
      intro request member before
      obtain ⟨⟨symbol, guard⟩, _, rfl⟩ := List.mem_map.mp member
      intro key entry body depth ordinary stored
      exact stored) state
    change NoNewMu state (run ((EqualityLeafProjectionWorkers.sequence (EqualityLeafProjectionNullary.requests rows)).bind makeNode) state).2
    rw [run_bind]
    exact noNewMu_trans first (makeNode_noNewMu _ _)
  let edges := run (EqualityLeafProjectionWorkers.sequence (EqualityLeafProjectionNullary.requests rows)) state
  have edgeFacts := EqualityLeafProjectionNullary.completed_rows rows state facts.coherent
  have linked := EqualityLeafProjectionNullary.rows_linked rows state facts.coherent facts.linked
  have normal : EqualityOrdinaryReadback.Normal result.2 result.1 := by
    have finalCoherent : Coherent (run (makeNode edges.1) edges.2).2 := by
      simpa only [result, computation, EqualityLeafProjectionNullary.build, run_bind] using resultFacts.coherent
    simpa only [result, computation, EqualityLeafProjectionNullary.build, run_bind] using
      EqualityOrdinaryReadback.makeNode_normal edges.1 edges.2 _ edgeFacts.1 linked finalCoherent
        (fun edge member => (edgeFacts.2.1 edge member).1) (grows_refl _)
  exact ⟨0, result.1, result.2, fun _ _ => rfl,
    ⟨resultFacts, prepared.preserve unchanged, (InternedConstructorTemplates.run_correct computation state facts.coherent.valid).2,
      InternedProbeProvenance.run_issued_extends computation state facts.coherent.valid⟩,
    checked.2, ⟨result.2, resultFacts, checked.2, normal⟩, build_leaf symbol row state facts⟩

/-- The endpoint row compiler executes the same nullary request sequence before its unary edge. -/
theorem rowAction_leaf (parent leaf : Fin symbols) (row : Row initial) :
    rowAction parent leaf row = MergedColdMerge.bind
      (MergedColdMerge.work (EqualityLeafProjectionNullary.build [(leaf, EqualityLeafProjectionLeafCache.constraint row)]))
      (fun child => MergedColdMerge.work (makeEdge parent (some [], .top) [child])) := by
  funext state
  simp only [rowAction, EqualityLeafProjectionNullary.build, EqualityLeafProjectionNullary.requests,
    List.map_cons, List.map_nil, EqualityLeafProjectionWorkers.sequence, run_bind, run,
    MergedColdMerge.bind, MergedColdMerge.work, Result.bind]

/-- Actual unary row construction has the requested generated row code. -/
theorem row_complete (parent leaf : Fin symbols) (row : Row initial)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state) :
    Complete (fun _ => rowAction parent leaf row) state
      (fun after edge => EdgeResident after edge ∧ RowShape parent leaf row edge) := by
  rw [rowAction_leaf]
  apply bind_complete _ _ state _ _ (leaf_complete leaf row state facts prepared)
  intro child after extension property
  have children : Values after [child] := by intro value member; simpa only [List.mem_singleton.mp member] using property.1
  have verified := edge_verified parent (some [], .top) [child] after extension.facts children
  have fields := MergedPhysicalGroupEdges.makeEdge_fields after extension.facts parent (some [], .top) [child] children
  apply MergedColdMergeSoundness.work_post _ after extension.prepared EdgeResident _ verified
    (by intro key entry body depth ordinary stored; exact stored)
  exact ⟨verified.result _ _ rfl, fields.1, fields.2.1, child, fields.2.2, property.2.2, property.2.1⟩

/-- Compiling a generated endpoint derives its exact row set in the actual returned cache. -/
theorem compile_complete (parent leaf : Fin symbols) (selected : Node initial)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state) :
    Complete (fun _ => compile parent leaf selected) state
      (fun after result => Available after result ∧ Replayable result ∧ NodeShape parent leaf selected result) := by
  have mapped := MergedColdMergeSoundness.map_related (fun _ => rowAction parent leaf)
    (fun _ (_ : Row initial) => True)
    (fun state row edge => EdgeResident state edge ∧ RowShape parent leaf row edge)
    (fun _ _ _ _ _ => trivial)
    (fun before after extension row edge valid => ⟨edge_grows before after extension.growth edge valid.1, valid.2⟩)
    (choices selected) (fun row _ before facts prepared _ => row_complete parent leaf row before facts prepared)
    state facts prepared (by simp)
  apply bind_complete _ _ state _ _ mapped
  intro edges after extension related
  have resident : Edges after edges := EnumerationSoundness.all₂_outputs _ _ _ (related.imp (fun _ _ property => property.1))
  have verified := node_verified edges after extension.facts resident
  let result := run (makeNode edges) after
  have available : Available result.2 result.1 := verified.result _ _ rfl
  have normal := EqualityOrdinaryReadback.makeNode_normal edges after result.2 extension.facts.coherent extension.facts.linked
    verified.facts.coherent resident (grows_refl _)
  have sound : ∀ edge ∈ edges, ∃ row, selected row ∧ RowShape parent leaf row edge := by
    intro edge member
    obtain ⟨row, included, shape⟩ := EqualityMergedTargetShape.related_member _ _ _ related edge member
    exact ⟨row, (choices_member selected row).mp included, shape.2⟩
  have membership : ∀ edge, edge ∈ nodeEdges result.1 ↔ edge ∈ edges := by
    intro edge
    rw [EqualityLeafProjectionPhysical.makeNode_edges edges after extension.facts.coherent extension.facts.linked resident,
      EqualityLeafProjectionPhysical.normalized_member after extension.facts.coherent edges resident]
    constructor
    · exact And.left
    · intro member
      obtain ⟨row, _, shape⟩ := sound edge member
      exact ⟨member, row_live parent leaf row edge shape⟩
  apply MergedColdMergeSoundness.work_post _ after extension.prepared Available _ verified (makeNode_noNewMu _ _)
  refine ⟨available, ⟨result.2, verified.facts, available, normal⟩, ?_⟩
  constructor
  · exact fun edge member => sound edge ((membership edge).mp member)
  · intro row selected
    obtain ⟨edge, member, property⟩ := related_input _ _ _ related row ((choices_member _ row).mpr selected)
    exact ⟨edge, (membership edge).mpr member, property.2⟩

/-- Compile each original endpoint occurrence in order and retain its exact finite index. -/
noncomputable def compileGroup (parent leaf : Fin symbols) (rows : Fin count → Node initial) :
    Action (Fin symbols) ConstraintKey (ValuesAt symbols count) :=
  MergedColdMerge.bind (MergedColdMerge.map (fun index => compile parent leaf (rows index)) (List.finRange count))
    (fun outputs => MergedColdMerge.pure (fun index => (outputs[index.val]?).getD .empty))

/-- Actual group compilation constructs the full endpoint representation invariant. -/
theorem compileGroup_complete (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state) :
    Complete (fun _ => compileGroup parent leaf rows) state (fun after values => Represents parent leaf after rows values) := by
  let post := fun state index value => Available state value ∧ Replayable value ∧ NodeShape parent leaf (rows index) value
  have mapped := MergedColdMergeSoundness.map_related (fun _ index => compile parent leaf (rows index))
    (fun _ (_ : Fin count) => True) post (fun _ _ _ _ _ => trivial)
    (fun before after extension index value valid => ⟨extension.available value valid.1, valid.2⟩)
    (List.finRange count) (fun index _ before facts prepared _ => compile_complete parent leaf (rows index) before facts prepared)
    state facts prepared (by simp)
  apply bind_complete _ _ state _ _ mapped
  intro values after extension related
  exact pure_complete _ after extension.facts extension.prepared _
    (fun index => related_index (post after) values related .empty index)

end MicroCFTA.EqualityNestedUnaryCompile
