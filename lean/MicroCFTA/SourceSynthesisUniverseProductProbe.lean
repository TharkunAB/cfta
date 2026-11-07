import MicroCFTA.SourceSynthesisUniverseProductProbeRows
import MicroCFTA.SourceSynthesisUniverseProbeReconstruction
import MicroCFTA.SourceRecursiveIntersectionMaybeMu

/-!
# Actual stored probe reconstruction from universe product rows

The actual product readback retains the original row order and children.
Its diagonal-cutoff replacement replays the resident probe edges and node.
Both the repaired stored executor and the optional-binder callback return
that complete probe without a constructor-cache effect.
-/
namespace MicroCFTA.SourceSynthesisUniverseProductProbe
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency InternedStoredSubstitution InternedStoredSubstitutionRebind
open InternedBinderProtocol (Reference NodeKey)
open SourceRecursiveIntersectionControl (pair repeatedValue)
open SourceSynthesisUniverseRowTransform (Readback)
open SourceSynthesisUniverseResidentRows (Rows)
open InternedNestedConstruction (Outcome work)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

omit [DecidableEq (EdgeKey String Guard)] in
private theorem product_fields (top : Guard) (uId : Nat) (marker : Value String Guard)
    (originals products : List (EdgeValue String Guard)) (closed : marker.free = [])
    (kinds : ∀ original ∈ originals, ∀ child ∈ original.children,
      child = marker ∨ child = .reference (.interned uId))
    (readback : All₂ (Readback top uId) originals products) :
    ∀ product ∈ products, product.entry.key.constraint = top ∧
      ∀ child ∈ product.children,
        child = marker ∨ child = .reference (.intersection (pair uId uId).1 (pair uId uId).2) := by
  have markerRead := InternedStoredSubstitutionScope.input_closed marker
    (replacement (.interned uId) (repeatedValue (pair uId uId))) closed
  revert kinds
  induction readback with
  | nil => intro _ product member; cases member
  | @cons original product originals products own rest ih =>
      intro kinds selected member
      rcases List.mem_cons.mp member with same | later
      · subst selected
        have projected := congrArg EdgeKey.constraint own.2
        refine ⟨projected, ?_⟩
        intro child present
        rw [own.1] at present
        change child ∈ original.children.map
          (input (replacement (.interned uId) (repeatedValue (pair uId uId)))) at present
        obtain ⟨before, included, mapped⟩ := List.mem_map.mp present
        rcases kinds original List.mem_cons_self before included with same | same
        · left
          rw [same, markerRead] at mapped
          exact mapped.symm
        · right
          simpa [same, input, replacement, repeatedValue] using mapped.symm
      · exact ih (fun row included => kinds row (List.mem_cons_of_mem _ included)) selected later

/-- Actual product rows reconstruct the complete resident probe in both source executors. -/
theorem execute_probe (top : Guard) (catalog : List (String × Nat)) (uId : Nat) (probe : Reference)
    (source : Value String Guard) (productEntry : Interned NodeKey)
    (products : List (EdgeValue String Guard)) (target : Value String Guard)
    (current : InternedConstructorTemplates.State String Guard) (facts : Facts current)
    (sourceAvailable : Available current source)
    (productAvailable : Available current
      (.node productEntry (canonicalEdges products) 0 [.intersection (pair uId uId).1 (pair uId uId).2]))
    (targetAvailable : Available current target)
    (sourceRows : Rows top catalog (.interned uId) source current)
    (targetRows : Rows top catalog probe target current)
    (readback : All₂ (Readback top uId) (nodeEdges source) products)
    (productResident : ∀ product ∈ products, EdgeResident current product) :
    InternedFreshOrdinaryStoredSubstitution.execute
      (.node productEntry (canonicalEdges products) 0 [.intersection (pair uId uId).1 (pair uId uId).2])
      (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe)) current =
        .done target current ∧
    SourceRecursiveIntersectionMaybeMu.callback (.intersection (pair uId uId).1 (pair uId uId).2)
      (.node productEntry (canonicalEdges products) 0 [.intersection (pair uId uId).1 (pair uId uId).2])
      probe current = .done target current := by
  obtain ⟨_sourceEntry, marker, targets, _sourceEq, _markerRead, _markerAvailable, closed,
      _originalTop, kinds, originalReplay, targetResident, nodeReplay⟩ :=
    SourceSynthesisUniverseProbeReconstruction.probe_targets top catalog (.interned uId) probe
      source target current facts sourceAvailable targetAvailable sourceRows targetRows
  have replayed := SourceSynthesisUniverseProductProbeRows.rows_replay top uId probe marker
    (nodeEdges source) products targets current closed kinds readback originalReplay
  have fields := product_fields top uId marker (nodeEdges source) products closed kinds readback
  have workDone := SourceSynthesisUniverseCanonicalRowReplay.execute_eq_work_of_raw top
    (.intersection (pair uId uId).1 (pair uId uId).2) productEntry products targets marker
    (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe))
    current facts productAvailable closed productResident targetResident
    (fun product member => (fields product member).1)
    (fun product member => (fields product member).2) replayed
  have done : InternedFreshOrdinaryStoredSubstitution.execute
      (.node productEntry (canonicalEdges products) 0 [.intersection (pair uId uId).1 (pair uId uId).2])
      (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe)) current =
        .done target current := by
    rw [workDone]
    simp only [work, nodeReplay]
  obtain ⟨_targetEntry, _targetMarker, _targetArrow, _targetRest, targetEq, _⟩ := targetRows
  refine ⟨done, ?_⟩
  simp only [SourceRecursiveIntersectionMaybeMu.callback, done, Outcome.bind, targetEq,
    withoutSelfReference, work, run]

end MicroCFTA.SourceSynthesisUniverseProductProbe
