import MicroCFTA.EqualityNestedUnaryAncestor

/-!
# Actual ancestor construction with indexed endpoint projection

The worker builds every original unary ancestor row in index order. It
then reads the normalized physical parent and projects its stored children.
The result represents the same original endpoint union, including removed
empty occurrences and repeated complete ancestor rows.
-/
namespace MicroCFTA.EqualityNestedUnaryAncestorCompile
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityMergedTargetReadback
open EqualityNestedUnarySchedule EqualityNestedUnaryAncestor

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Build one source parent and project child zero from its actual normalized rows. -/
noncomputable def compile (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count) :
    Action (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey × Value (Fin symbols) ConstraintKey) :=
  MergedColdMerge.bind (MergedColdMerge.map (fun index => MergedColdMerge.work
    (makeEdge (tags index).1 (tags index).2 [values index])) (List.finRange count)) fun edges =>
      MergedColdMerge.bind (MergedColdMerge.work (makeNode edges)) fun root =>
        MergedColdMerge.bind (MergedColdMerge.work (makeUnion (projected root))) fun projection =>
          MergedColdMerge.pure (root, projection)

/-- Actual ancestor requests derive original-index alignment and exact physical projection. -/
theorem compile_complete (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (values : ValuesAt symbols count) (tags : Fin count → Fin symbols × ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : Represents parent leaf state rows values) :
    Complete (fun _ => compile tags values) state (fun after result =>
      Available after result.1 ∧ Replayable result.1 ∧
      Available after result.2 ∧ Replayable result.2 ∧
      NodeShape parent leaf (EqualityFixedProjectionInvariant.project rows) result.2) := by
  let pre := fun state index => Available state (values index)
  let post := fun state index (edge : EdgeValue (Fin symbols) ConstraintKey) =>
    EdgeResident state edge ∧ edge.children = [values index]
  have mapped := MergedColdMergeSoundness.map_related
    (fun _ index => MergedColdMerge.work (makeEdge (tags index).1 (tags index).2 [values index])) pre post
    (fun _ _ extension index valid => extension.available _ valid)
    (fun before after extension index edge valid => ⟨edge_grows before after extension.growth edge valid.1, valid.2⟩)
    (List.finRange count) (fun index _ before facts prepared valid => by
      have inputs : Values before [values index] := by
        intro value member
        simpa only [List.mem_singleton.mp member] using valid
      have verified := edge_verified (tags index).1 (tags index).2 [values index] before facts inputs
      apply MergedColdMergeSoundness.work_post _ before prepared EdgeResident _ verified
        (by intro key entry body depth ordinary stored; exact stored)
      exact ⟨verified.result _ _ rfl,
        (MergedPhysicalGroupEdges.makeEdge_fields before facts (tags index).1 (tags index).2 [values index] inputs).2.2⟩)
    state facts prepared (fun index _ => (represented index).1)
  unfold compile
  apply bind_complete _ _ state _ _ mapped
  intro edges afterEdges edgeExtension related
  have resident : Edges afterEdges edges :=
    EnumerationSoundness.all₂_outputs _ _ _ (related.imp (fun _ _ valid => valid.1))
  have aligned := related.imp (fun _ _ valid => valid.2)
  have verified := node_verified edges afterEdges edgeExtension.facts resident
  let root := run (makeNode edges) afterEdges
  have rootAvailable : Available root.2 root.1 := verified.result _ _ rfl
  have rootNormal := EqualityOrdinaryReadback.makeNode_normal edges afterEdges root.2
    edgeExtension.facts.coherent edgeExtension.facts.linked verified.facts.coherent resident (grows_refl _)
  have rootComplete := MergedColdMergeSoundness.work_post (makeNode edges) afterEdges edgeExtension.prepared
    Available (fun after result => Available after result ∧ Replayable result ∧ result = root.1)
    verified (makeNode_noNewMu _ _) ⟨rootAvailable, ⟨root.2, verified.facts, rootAvailable, rootNormal⟩, rfl⟩
  apply bind_complete _ _ afterEdges _ _ rootComplete
  intro value afterRoot rootExtension valid
  have later := represents_grows parent leaf state afterRoot (edgeExtension.trans rootExtension) rows values represented
  have projection := projected_complete parent leaf rows values edges aligned afterEdges afterRoot
    edgeExtension.facts.coherent edgeExtension.facts.linked resident rootExtension.facts rootExtension.prepared later
  rw [← valid.2.2] at projection
  apply bind_complete _ _ afterRoot _ _ projection
  intro output after projectionExtension outputValid
  exact pure_complete (value, output) after projectionExtension.facts projectionExtension.prepared _
    ⟨projectionExtension.available value valid.1, valid.2.1, outputValid⟩

/-- Keep the actual ancestor and run the current target merge on its physical projection. -/
noncomputable def target (tags : Fin count → Fin symbols × ConstraintKey) (values : ValuesAt symbols count)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    Action (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey × Value (Fin symbols) ConstraintKey) :=
  MergedColdMerge.bind (compile tags values) fun result =>
    MergedColdMerge.bind (execute MergedSourceGrouping.groups clear top comparison result.2) fun merged =>
      MergedColdMerge.pure (result.1, merged)

/-- The source target computed through actual ancestors retains the indexed nested endpoint meaning. -/
theorem target_complete (parent leaf : Fin symbols) (rows : Fin count → Node initial)
    (values : ValuesAt symbols count) (tags : Fin count → Fin symbols × ConstraintKey)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (represented : Represents parent leaf state rows values)
    (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    Complete (fun _ => target tags values clear top comparison) state (fun after result =>
      Available after result.1 ∧ Replayable result.1 ∧
      Available after result.2 ∧ Replayable result.2 ∧
      NodeShape parent leaf (EqualityFixedProjectionInvariant.project rows) result.2) := by
  unfold target
  apply bind_complete _ _ state _ _ (compile_complete parent leaf rows values tags state facts prepared represented)
  intro result after extension valid
  have fixed := EqualityNestedUnaryBound.merge_fixed parent leaf _ result.2 small valid.2.2.2.2 valid.2.2.2.1
    after extension.facts extension.prepared valid.2.2.1 clear top comparison
  refine ⟨0, result, after, ?_, .refl after extension.facts extension.prepared, valid⟩
  intro _ _
  simp only [MergedColdMerge.bind, fixed, MergedSourceComparison.Result.bind, MergedColdMerge.pure]

end MicroCFTA.EqualityNestedUnaryAncestorCompile
