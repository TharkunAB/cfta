import MicroCFTA.SourceSynthesisCurrentUniverseOwnership
import MicroCFTA.SourceSynthesisUniverseMappedProbeRows

/-!
# Both actual current universe probes in the same source heap

The same completed source build supplies Facts and both probe callbacks.
C8 derives each callback's complete row packet in that same heap.
Both probes retain the same complete source marker.
The false selector chooses Depth. The true selector chooses the exact
ordinary name selected from the full stored Depth value.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseProbeRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (NodeKey Reference)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open SourceSynthesisTypeSyntax (Library Query allTypesBody)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The same stored writer derives both full probe packets with one actual complete marker. -/
theorem current_stored_universe_probe_rows
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
    (key : NodeKey) (owner : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : heap.nodeRecords key = some (.mu owner body depth ordinary)) :
    InternedNestedFacts.Facts heap ∧
      ∃ (markerEntry : Interned NodeKey) (markerRow : EdgeValue Symbol Guard),
        let marker : Value Symbol Guard := .node markerEntry [markerRow] 0 []
        markerRow.children = [] ∧ markerRow.entry.key = ⟨literal "(->)", [], top⟩ ∧
        marker.free = [] ∧ Available heap marker ∧
        ∀ ordinaryProbe : Bool,
          let probe : Reference := if ordinaryProbe then .uninterned (ordinaryLevel depth) else .depth
          let value : Value Symbol Guard := if ordinaryProbe then ordinary else depth
          ∃ (entry : Interned NodeKey) (arrow : EdgeValue Symbol Guard) (rows : List (EdgeValue Symbol Guard)),
            callback (ordinarySymbols (allTypesBody top
              (SourceSynthesisCurrentContext.constructorCatalog lib query))) [] probe heap = .done value heap ∧
            value = .node entry (canonicalEdges (arrow :: rows)) 0 [probe] ∧
            arrow.children = [marker, .reference probe, .reference probe] ∧
            arrow.entry.key = ⟨literal "->", [marker.referenceOf, .ref probe, .ref probe], top⟩ ∧
            Language.All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
              row.children = List.replicate descriptor.2 (.reference probe) ∧
              row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref probe), top⟩)
              (SourceSynthesisUniverseBody.descriptors
                (SourceSynthesisCurrentContext.constructorCatalog lib query)) rows ∧
            Available heap value ∧
            (∀ row ∈ arrow :: rows, EdgeResident heap row) ∧
            (∀ row ∈ canonicalEdges (arrow :: rows), row.entry.key.constraint = top ∧
              ∀ child ∈ row.children, child = marker ∨ child = .reference probe) ∧
            arrow ∈ canonicalEdges (arrow :: rows) := by
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, Outcome.state] using checked.facts
  obtain ⟨_bodyEntry, sourceMarker, _bodyArrow, _bodyRows, _bodyEq, sourceMarkerRead,
      _bodyChildren, _bodyKey, _bodyAligned, _sourceMarkerClosed, sourceMarkerAvailable, _bodyFields, _bodyRetained⟩ :=
    SourceSynthesisCurrentUniverseOwnership.current_stored_universe_rows
      lib query signed whole accepted rootValue heap built key owner body depth ordinary stored
  obtain ⟨markerEntry, markerRow, markerEq, leaf, markerKey⟩ := sourceMarkerRead
  let marker : Value Symbol Guard := .node markerEntry [markerRow] 0 []
  have markerClosed : marker.free = [] := rfl
  have markerAvailable : Available heap marker := markerEq ▸ sourceMarkerAvailable
  have replay := SourceSynthesisCurrentUniverseOwnership.current_stored_universe_source_probes
    lib query signed whole accepted rootValue heap built key owner body depth ordinary stored heap (grows_refl heap)
  refine ⟨facts, markerEntry, markerRow, leaf, markerKey, markerClosed, markerAvailable, ?_⟩
  intro ordinaryProbe
  let probe : Reference := if ordinaryProbe then .uninterned (ordinaryLevel depth) else .depth
  let value : Value Symbol Guard := if ordinaryProbe then ordinary else depth
  have available : Available heap (.reference probe) := by
    cases ordinaryProbe with
    | false => exact InternedNestedProvenance.depth_available heap
    | true => exact InternedNestedProvenance.ordinary_available heap (ordinaryLevel depth)
  have observed : callback (ordinarySymbols (allTypesBody top
      (SourceSynthesisCurrentContext.constructorCatalog lib query))) [] probe heap = .done value heap := by
    cases ordinaryProbe with
    | false => exact replay.1
    | true => exact replay.2
  obtain ⟨entry, probeMarker, arrow, rows, final, called, probeMarkerRead, children, arrowKey,
      aligned, _finalFacts, nodeAvailable, resident, _probeMarkerClosed, probeMarkerAvailable, fields, retained⟩ :=
    SourceSynthesisCurrentUniverseBody.current_types_callback_rows lib query probe heap facts available
  have same := Outcome.done.inj (called.symm.trans observed)
  have heapSame : final = heap := same.2
  subst final
  obtain ⟨probeMarkerEntry, probeMarkerRow, probeMarkerEq, _probeLeaf, probeMarkerKey⟩ := probeMarkerRead
  have nativeProbeMarkerAvailable : Available heap (.node probeMarkerEntry [probeMarkerRow] 0 []) :=
    probeMarkerEq ▸ probeMarkerAvailable
  have sameNative := SourceSynthesisUniverseMappedProbeRows.marker_eq (literal "(->)") top
    probeMarkerEntry markerEntry probeMarkerRow markerRow heap facts
    nativeProbeMarkerAvailable markerAvailable probeMarkerKey markerKey
  have markerSame : probeMarker = marker := probeMarkerEq.trans sameNative
  rw [markerSame] at children arrowKey fields
  have valueSame : value = .node entry (canonicalEdges (arrow :: rows)) 0 [probe] := same.1.symm
  refine ⟨entry, arrow, rows, observed, valueSame, children, arrowKey,
    aligned, ?_, resident, fields, retained⟩
  rw [valueSame]
  exact nodeAvailable

#print axioms current_stored_universe_probe_rows

end MicroCFTA.SourceSynthesisCurrentUniverseProbeRows
