import MicroCFTA.SourceSynthesisCurrentUniverseReferenceIdentity
import MicroCFTA.SourceEqualityNativeDemand

/-!
# Canonical source U from an actual open product

The source build supplies both stored probes and the original Mu record.
The product readback supplies the exact transformed source rows.
Actual optional construction returns the original U without changing the state.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeOpenProductReclosure
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency InternedFreshProbeKeys
open InternedNestedConstruction (Outcome finish)
open InternedBinderProtocol (NodeKey Reference)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "Checked" => SourceEqualityNativeDemand.State

set_option autoImplicit false

/-- Source probes reclose the exact open row product to the original stored U. -/
theorem stored_open_product_optional_reclosure
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (state : Checked width) (facts : Facts state.native.machine.heap)
    (growth : Grows sourceHeap state.native.machine.heap)
    (cutoffKey : Nat × Nat) (product : Value Symbol Guard)
    (productEntry : Interned NodeKey) (products : List (EdgeValue Symbol Guard))
    (productRead : product = .node productEntry (canonicalEdges products) 0
      [.intersection cutoffKey.1 cutoffKey.2])
    (productAvailable : Available state.native.machine.heap product)
    (readback : All₂ (fun (source : EdgeValue Symbol Guard) target =>
      target.children = source.children.map (input (replacement (.interned entry.identity)
        (.reference (.intersection cutoffKey.1 cutoffKey.2)))) ∧
      target.entry.key = ⟨source.entry.key.symbol,
        (source.children.map (input (replacement (.interned entry.identity)
          (.reference (.intersection cutoffKey.1 cutoffKey.2))))).map Value.referenceOf, top⟩)
      (match body with | .node _ rows _ _ => rows | _ => []) products)
    (productResident : ∀ row ∈ products, EdgeResident state.native.machine.heap row) :
    SourceRecursiveIntersectionMaybeMu.maybeMu cutoffKey product state.native.machine.heap =
      .done (.mu entry body depth ordinary) state.native.machine.heap ∧
    SourceEqualityNativeDemand.step (.code (.optionalBinder cutoffKey product .pure)) state =
      .yielded (.code (.pure (.mu entry body depth ordinary))) state ∧
    SourceEqualityNativeDemand.execute 2 (.code (.optionalBinder cutoffKey product .pure)) state =
      .done (.mu entry body depth ordinary) state := by
  let heap := state.native.machine.heap
  let cutoff : Reference := .intersection cutoffKey.1 cutoffKey.2
  have universeAvailable : Available heap (.mu entry body depth ordinary) :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have referenceAvailable : Available heap (.reference (.interned entry.identity)) :=
    InternedProbeProvenance.reference_available_mu heap facts entry body depth ordinary universeAvailable
  have bodyReplay := SourceSynthesisCurrentUniverseOwnership.current_stored_universe_body_replay
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored heap growth
  obtain ⟨b, marker, arrow, rows, finalBody, calledBody, markerRead, arrowChildren, arrowKey,
      catalogRows, _bodyFacts, _bodyAvailable, sourceResident, _markerClosed, markerAvailable,
      coarseKinds, _arrowMember⟩ :=
    SourceSynthesisCurrentUniverseBody.current_types_callback_rows
      lib query (.interned entry.identity) heap facts referenceAvailable
  have sameBody := Outcome.done.inj (calledBody.symm.trans bodyReplay)
  have heapSame : finalBody = heap := sameBody.2
  subst finalBody
  have bodyEq : body = .node b (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity] := sameBody.1.symm
  obtain ⟨m, markerRow, markerEq, _leaf, markerKey⟩ := markerRead
  have nativeMarker : Available heap (.node m [markerRow] 0 []) := by
    rw [← markerEq]
    exact markerAvailable
  have nativeArrowChildren : arrow.children =
      [.node m [markerRow] 0 [], .reference (.interned entry.identity), .reference (.interned entry.identity)] := by
    simpa only [markerEq] using arrowChildren
  have nativeArrowKey : arrow.entry.key = ⟨literal "->",
      [(Value.node m [markerRow] 0 []).referenceOf, .ref (.interned entry.identity), .ref (.interned entry.identity)], top⟩ := by
    simpa only [markerEq] using arrowKey
  have bodyChildren : ∀ row ∈ canonicalEdges (arrow :: rows), ∀ child ∈ row.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned entry.identity) := by
    intro row member child included
    simpa only [markerEq] using (coarseKinds row member).2 child included
  have aligned : All₂ (fun (source : EdgeValue Symbol Guard) target =>
      target.children = source.children.map (input (replacement (.interned entry.identity) (.reference cutoff))) ∧
      target.entry.key = ⟨source.entry.key.symbol,
        (source.children.map (input (replacement (.interned entry.identity) (.reference cutoff)))).map Value.referenceOf,
        top⟩) (canonicalEdges (arrow :: rows)) products := by
    simpa only [bodyEq] using readback
  have productNodeAvailable : Available heap (.node productEntry (canonicalEdges products) 0 [cutoff]) := by
    rw [← productRead]
    exact productAvailable
  obtain ⟨_probeFacts, probeMarkerEntry, probeMarkerRow, _probeLeaf, probeMarkerKey,
      _probeMarkerClosed, probeMarkerAvailable, probePackets⟩ :=
    SourceSynthesisCurrentUniverseProbeRows.current_stored_universe_probe_rows
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
  have probeMarkerResident : sourceHeap.nodeRecords probeMarkerEntry.key =
      some (.node probeMarkerEntry [probeMarkerRow] 0 []) :=
    probeMarkerAvailable.resident probeMarkerEntry rfl
  have currentProbeMarker : Available heap (.node probeMarkerEntry [probeMarkerRow] 0 []) :=
    facts.cached.nodes probeMarkerEntry.key _ (growth.nodeRecords _ _ probeMarkerResident)
  have probeMarkerSame : Value.node probeMarkerEntry [probeMarkerRow] 0 [] = .node m [markerRow] 0 [] :=
    SourceSynthesisUniverseMappedProbeRows.marker_eq (literal "(->)") top
      probeMarkerEntry m probeMarkerRow markerRow heap facts currentProbeMarker nativeMarker probeMarkerKey markerKey
  have nativeClosed : (Value.node m [markerRow] 0 []).free = [] := rfl
  have nativeNonempty : (Value.node m [markerRow] 0 []).referenceOf ≠ .empty := by simp [Value.referenceOf]
  have probeCallbacks : ∀ ordinaryProbe : Bool,
      let probe : Reference := if ordinaryProbe then .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth) else .depth
      let target : Value Symbol Guard := if ordinaryProbe then ordinary else depth
      SourceRecursiveIntersectionMaybeMu.callback cutoff product probe heap = .done target heap := by
    intro ordinaryProbe
    let probe : Reference := if ordinaryProbe then .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth) else .depth
    let target : Value Symbol Guard := if ordinaryProbe then ordinary else depth
    obtain ⟨probeEntry, probeArrow, probeRows, _probeCalled, probeEq, probeChildren, probeKey,
        probeAligned, _probeAvailable, probeResident, _probeKinds, _probeRetained⟩ := probePackets ordinaryProbe
    have nativeProbeChildren : probeArrow.children = [.node m [markerRow] 0 [], .reference probe, .reference probe] := by
      simpa only [probeMarkerSame] using probeChildren
    have nativeProbeKey : probeArrow.entry.key = ⟨literal "->", [(Value.node m [markerRow] 0 []).referenceOf,
        .ref probe, .ref probe], top⟩ := by
      simpa only [probeMarkerSame] using probeKey
    have probeCurrent : ∀ row ∈ probeArrow :: probeRows, EdgeResident heap row := by
      intro row member
      exact edge_grows sourceHeap heap growth row (probeResident row member)
    have targetAvailable : Available heap target := by
      cases ordinaryProbe with
      | false => exact universeAvailable.children depth (by simp [InternedProbeProvenance.children])
      | true => exact universeAvailable.children ordinary (by simp [InternedProbeProvenance.children])
    have replayed := SourceSynthesisCurrentUniverseReferenceIdentity.mixed_product_probe_at literal top
      (SourceSynthesisUniverseBody.descriptors (SourceSynthesisCurrentContext.constructorCatalog lib query))
      entry.identity cutoff probe (.node m [markerRow] 0 []) arrow rows probeEntry probeArrow probeRows target
      productEntry products heap facts nativeClosed nativeNonempty nativeArrowChildren nativeArrowKey
      catalogRows nativeProbeChildren nativeProbeKey probeAligned sourceResident probeCurrent probeEq productNodeAvailable
      targetAvailable bodyChildren aligned productResident
    rw [productRead]
    exact replayed.2
  have depthCallback : SourceRecursiveIntersectionMaybeMu.callback cutoff product .depth heap =
      .done depth heap := probeCallbacks false
  have ordinaryCallback : SourceRecursiveIntersectionMaybeMu.callback cutoff product
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) heap =
        .done ordinary heap := probeCallbacks true
  dsimp only [cutoff] at depthCallback ordinaryCallback
  obtain ⟨_keySame, table, record⟩ := available_mu_key heap facts entry body depth ordinary universeAvailable
  have kept : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
    simp [finish, cleanup, bodyEq, Value.free, Value.referenceOf]
  have pendingMember : Reference.intersection cutoffKey.1 cutoffKey.2 ∈ product.free := by
    simp only [productRead, Value.free, List.mem_singleton]
  have completed : SourceRecursiveIntersectionMaybeMu.maybeMu cutoffKey product heap =
      .done (.mu entry body depth ordinary) heap := by
    simp only [SourceRecursiveIntersectionMaybeMu.maybeMu, ite_eq_left pendingMember,
      SourceRecursiveIntersectionMaybeMu.construct, depthCallback, Outcome.bind, ordinaryCallback,
      InternedNestedConstruction.request, table, record, kept]
  have one : SourceEqualityNativeDemand.step (.code (.optionalBinder cutoffKey product .pure)) state =
      .yielded (.code (.pure (.mu entry body depth ordinary))) state := by
    simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
      completed, SourceEqualityNativeDemand.lift]
    rfl
  refine ⟨completed, one, ?_⟩
  rw [SourceEqualityNativeDemand.execute, one]
  rfl

end MicroCFTA.SourceCurrentAllocatedNativeOpenProductReclosure
