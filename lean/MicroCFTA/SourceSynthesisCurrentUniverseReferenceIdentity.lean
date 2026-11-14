import MicroCFTA.SourceSynthesisUniverseOffDiagonalBody
import MicroCFTA.SourceSynthesisUniverseProbeCutoffComposition
import MicroCFTA.SourceSynthesisCurrentUniverseProbeRows
import MicroCFTA.SourceSynthesisUniverseMappedBodyExactFree
import MicroCFTA.SourceSynthesisUniverseProductProbeRows
import MicroCFTA.SourceSynthesisUniverseCanonicalRowReplay
import MicroCFTA.SourceSynthesisUniverseNodeReplay
import MicroCFTA.SourceSynthesisUniverseReferenceIdentityJoin
import MicroCFTA.SourceSynthesisUniverseTopConjunction
import MicroCFTA.SourceRecursiveIntersectionKernelCoverage
import MicroCFTA.SourceRecursiveIntersectionKernelStability
import MicroCFTA.SourceRecursiveIntersectionKernelScope

/-!
# Exact open-universe identity in the actual current source heap

The same stored writer supplies the body and both complete probes.
The actual native body product supplies its transformed source rows.
Probe substitution replays the original values in the same grown heap.
The outer optional binder therefore reuses the original complete Mu.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseReferenceIdentity
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency InternedFreshProbeKeys
open InternedRecordCoherence (Covered)
open InternedNestedConstruction (Outcome finish)
open InternedBinderProtocol (NodeKey Reference)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseRowTransform (Readback)
open SourceSynthesisUniverseBodyReferenceControl (second secondState)
open SourceSynthesisTypeSyntax (Library Query allTypesBody)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)

set_option autoImplicit false

section Generic
variable {Symbol Guard : Type}

private theorem aligned_output {A B : Type} {relation : A → B → Prop}
    {inputs : List A} {outputs : List B} (aligned : All₂ relation inputs outputs) :
    ∀ output ∈ outputs, ∃ input ∈ inputs, relation input output := by
  induction aligned with
  | nil => intro output member; cases member
  | @cons input output inputs outputs own tail ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨input, List.mem_cons_self, own⟩
      · obtain ⟨input, member, related⟩ := ih selected later
        exact ⟨input, List.mem_cons_of_mem _ member, related⟩

private theorem product_fields (top : Guard) (uId : Nat) (marker : Value Symbol Guard)
    (originals products : List (EdgeValue Symbol Guard)) (closed : marker.free = [])
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

private theorem mapped_product_probe [DecidableEq (EdgeKey Symbol Guard)]
    (literal : String → Symbol) (top : Guard) (catalog : List (String × Nat))
    (uId : Nat) (probe : Reference) (marker : Value Symbol Guard)
    (sourceArrow : EdgeValue Symbol Guard) (sources : List (EdgeValue Symbol Guard))
    (targetEntry : Interned NodeKey) (targetArrow : EdgeValue Symbol Guard)
    (targets : List (EdgeValue Symbol Guard)) (target : Value Symbol Guard)
    (productEntry : Interned NodeKey) (products : List (EdgeValue Symbol Guard))
    (current : State Symbol Guard) (facts : Facts current)
    (closed : marker.free = []) (nonemptyMarker : marker.referenceOf ≠ .empty)
    (sourceChildren : sourceArrow.children = [marker, .reference (.interned uId), .reference (.interned uId)])
    (sourceKey : sourceArrow.entry.key =
      ⟨literal "->", [marker.referenceOf, .ref (.interned uId), .ref (.interned uId)], top⟩)
    (sourceAligned : All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
      row.children = List.replicate descriptor.2 (.reference (.interned uId)) ∧
      row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref (.interned uId)), top⟩) catalog sources)
    (targetChildren : targetArrow.children = [marker, .reference probe, .reference probe])
    (targetKey : targetArrow.entry.key = ⟨literal "->", [marker.referenceOf, .ref probe, .ref probe], top⟩)
    (targetAligned : All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
      row.children = List.replicate descriptor.2 (.reference probe) ∧
      row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref probe), top⟩) catalog targets)
    (sourceResident : ∀ row ∈ sourceArrow :: sources, EdgeResident current row)
    (targetResident : ∀ row ∈ targetArrow :: targets, EdgeResident current row)
    (targetEq : target = .node targetEntry (canonicalEdges (targetArrow :: targets)) 0 [probe])
    (productAvailable : Available current
      (.node productEntry (canonicalEdges products) 0 [.intersection (pair uId uId).1 (pair uId uId).2]))
    (targetAvailable : Available current target)
    (sourceKinds : ∀ row ∈ canonicalEdges (sourceArrow :: sources), ∀ child ∈ row.children,
      child = marker ∨ child = .reference (.interned uId))
    (readback : All₂ (Readback top uId) (canonicalEdges (sourceArrow :: sources)) products)
    (productResident : ∀ row ∈ products, EdgeResident current row) :
    InternedFreshOrdinaryStoredSubstitution.execute
      (.node productEntry (canonicalEdges products) 0 [.intersection (pair uId uId).1 (pair uId uId).2])
      (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe)) current =
        .done target current ∧
    SourceRecursiveIntersectionMaybeMu.callback (.intersection (pair uId uId).1 (pair uId uId).2)
      (.node productEntry (canonicalEdges products) 0 [.intersection (pair uId uId).1 (pair uId uId).2])
      probe current = .done target current := by
  have replayed := SourceSynthesisUniverseMappedProbeRows.raw_rows_replay literal top (.interned uId) probe marker
    sourceArrow targetArrow catalog sources targets current facts closed sourceChildren sourceKey targetKey
    sourceAligned targetAligned targetResident
  obtain ⟨canonicalTargets, canonicalReplay, _members, canonicalResident, sameNode⟩ :=
    SourceSynthesisUniverseCanonicalRowReplay.canonical_replay top
      (replacement (.interned uId) (.reference probe)) (sourceArrow :: sources) (targetArrow :: targets)
      current facts sourceResident targetResident replayed
  have targetLive : ∀ row ∈ targetArrow :: targets,
      row.children.any (fun child => child.referenceOf == .empty) = false := by
    have catalogLive : ∀ row ∈ targets,
        row.children.any (fun child => child.referenceOf == .empty) = false := by
      intro row member
      obtain ⟨descriptor, _included, related⟩ := aligned_output targetAligned row member
      simp [related.1, Value.referenceOf]
    intro row member
    rcases List.mem_cons.mp member with rfl | later
    · simp [targetChildren, Value.referenceOf]
      exact nonemptyMarker
    · exact catalogLive row later
  have survivingTargets : surviving (targetArrow :: targets) = targetArrow :: targets := by
    unfold surviving
    apply List.filter_eq_self.mpr
    intro row member
    simp only [targetLive row member, Bool.not_false]
  have retained : targetArrow ∈ canonicalEdges (targetArrow :: targets) :=
    canonicalEdges_retains current facts.coherent _ targetArrow targetResident List.mem_cons_self
  have targetNonempty : canonicalEdges (surviving (targetArrow :: targets)) ≠ [] := by
    rw [survivingTargets]
    intro absent
    simp only [absent, List.not_mem_nil] at retained
  have targetNodeAvailable : Available current
      (.node targetEntry (canonicalEdges (surviving (targetArrow :: targets))) 0 [probe]) := by
    rw [survivingTargets, ← targetEq]
    exact targetAvailable
  have targetNode := SourceSynthesisUniverseNodeReplay.resident_node_replay
    (targetArrow :: targets) targetEntry 0 [probe] current facts targetNodeAvailable targetNonempty
  have nodeReplay : run (makeNode canonicalTargets) current = (target, current) := by
    rw [sameNode]
    simpa only [survivingTargets, ← targetEq] using targetNode
  have rowsReplay := SourceSynthesisUniverseProductProbeRows.rows_replay top uId probe marker
    (canonicalEdges (sourceArrow :: sources)) products canonicalTargets current closed sourceKinds readback canonicalReplay
  have fields := product_fields top uId marker (canonicalEdges (sourceArrow :: sources)) products closed sourceKinds readback
  have workDone := SourceSynthesisUniverseCanonicalRowReplay.execute_eq_work_of_raw top
    (.intersection (pair uId uId).1 (pair uId uId).2) productEntry products canonicalTargets marker
    (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe)) current facts productAvailable
    closed productResident canonicalResident (fun row member => (fields row member).1)
    (fun row member => (fields row member).2) rowsReplay
  have done : InternedFreshOrdinaryStoredSubstitution.execute
      (.node productEntry (canonicalEdges products) 0 [.intersection (pair uId uId).1 (pair uId uId).2])
      (replacement (.intersection (pair uId uId).1 (pair uId uId).2) (.reference probe)) current =
        .done target current := by
    rw [workDone]
    simp only [InternedNestedConstruction.work, nodeReplay]
  refine ⟨done, ?_⟩
  simp only [SourceRecursiveIntersectionMaybeMu.callback, done, Outcome.bind, targetEq,
    withoutSelfReference, InternedNestedConstruction.work, run]

private theorem available_mu_key (state : State Symbol Guard) (facts : Facts state)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available state (.mu entry body depth ordinary)) :
    entry.key = muKey depth ordinary ∧ state.nodes.table (muKey depth ordinary) = some entry ∧
      state.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) := by
  have resident := available.resident entry rfl
  obtain ⟨stored, present, fields⟩ := facts.coherent.nodes entry.key _ resident
  change entry = stored ∧ entry.key = muKey depth ordinary at fields
  rw [← fields.1] at present
  exact ⟨fields.2, fields.2 ▸ present, fields.2 ▸ resident⟩

private theorem reference_available_mu (state : State Symbol Guard) (facts : Facts state)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available state (.mu entry body depth ordinary)) :
    Available state (.reference (.interned entry.identity)) := by
  have installed := resident_entry state facts.coherent (.mu entry body depth ordinary) available.resident entry rfl
  have issued := (facts.coherent.valid.2.2 entry.key entry installed).2
  apply reference_available
  intro identity member
  have same : identity = entry.identity := by simpa [Value.free] using member
  subst identity
  exact ⟨entry.key, issued⟩

end Generic

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- The actual universe request returns its original Mu after valid source heap growth. -/
theorem current_stored_universe_reference_identity_after_growth
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (cacheValid : Cache.Valid domains) :
    let initial : Machine Symbol Guard := ⟨heap, domains⟩
    ∃ final : Machine Symbol Guard,
      execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
          .done (.mu entry body depth ordinary) final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧ Extension initial final ∧
      Available final.heap (.mu entry body depth ordinary) ∧ Available final.heap rootValue ∧
      final.heap.nodeRecords key = some (.mu entry body depth ordinary) ∧
      (∀ extra, execute top SourceEqualityPCSNativeEdge.conjoin (13 + extra) IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
          .done (.mu entry body depth ordinary) final) ∧
      (∀ pending, Covered pending heap → Covered pending final.heap) ∧
      (SourceRecursiveIntersectionSemanticHeap.SemanticHeap heap →
        SourceRecursiveIntersectionSemanticHeap.SemanticHeap final.heap) := by
  let initial : Machine Symbol Guard := ⟨heap, domains⟩
  have sourceGrowth : Grows sourceHeap heap := growth
  have storedNow : heap.nodeRecords key = some (.mu entry body depth ordinary) :=
    sourceGrowth.nodeRecords key _ stored
  have rootReplay := InternedFreshOrdinaryReplay.empty_replay
    (ordinarySymbols whole) rootValue sourceHeap heap built sourceGrowth
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] heap facts
    (by intro value member; cases member)
  have rootAvailable : Available heap rootValue := checked.result rootValue heap rootReplay
  have universeAvailable : Available heap (.mu entry body depth ordinary) := facts.cached.nodes key _ storedNow
  have referenceAvailable : Available heap (.reference (.interned entry.identity)) :=
    reference_available_mu heap facts entry body depth ordinary universeAvailable
  have bodyReplay := SourceSynthesisCurrentUniverseOwnership.current_stored_universe_body_replay
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored heap sourceGrowth
  obtain ⟨b, marker, arrow, rows, finalBody, calledBody, markerRead, arrowChildren, arrowKey,
      catalogRows, _bodyFacts, _bodyAvailable, sourceResident, _markerClosed, markerAvailable, coarseKinds, arrowMember⟩ :=
    SourceSynthesisCurrentUniverseBody.current_types_callback_rows
      lib query (.interned entry.identity) heap facts referenceAvailable
  have sameBody := Outcome.done.inj (calledBody.symm.trans bodyReplay)
  have bodyHeap : finalBody = heap := sameBody.2
  subst finalBody
  have bodyEq : body = .node b (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity] := sameBody.1.symm
  let bodyRows := canonicalEdges (arrow :: rows)
  obtain ⟨m, markerRow, markerEq, leaf, markerKey⟩ := markerRead
  have nativeUniverse : Available initial.heap
      (.mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    simpa only [bodyEq, bodyRows] using universeAvailable
  have nativeMarker : Available initial.heap (.node m [markerRow] 0 []) := by
    change Available heap (.node m [markerRow] 0 [])
    rw [← markerEq]
    exact markerAvailable
  have markerTop : markerRow.entry.key.constraint = top := congrArg EdgeKey.constraint markerKey
  have nativeArrowChildren : arrow.children = [.node m [markerRow] 0 [],
      .reference (.interned entry.identity), .reference (.interned entry.identity)] := by
    simpa only [markerEq] using arrowChildren
  have nativeArrowKey : arrow.entry.key = ⟨literal "->", [(Value.node m [markerRow] 0 []).referenceOf,
      .ref (.interned entry.identity), .ref (.interned entry.identity)], top⟩ := by
    simpa only [markerEq] using arrowKey
  have bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top := fun row member => (coarseKinds row member).1
  have bodyChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned entry.identity) := by
    intro row member child included
    simpa only [markerEq] using (coarseKinds row member).2 child included
  have classified := SourceSynthesisUniverseMappedBodyCanonical.canonical_row_kinds
    (literal "->") literal top entry.identity (.node m [markerRow] 0 []) arrow
    (SourceSynthesisUniverseBody.descriptors (SourceSynthesisCurrentContext.constructorCatalog lib query)) rows
    nativeArrowChildren nativeArrowKey catalogRows
  have nativeKinds : ∀ source ∈ bodyRows,
      (source.children = [.node m [markerRow] 0 [], .reference (.interned entry.identity),
          .reference (.interned entry.identity)] ∧
        source.entry.key = ⟨literal "->", [(Value.node m [markerRow] 0 []).referenceOf,
          .ref (.interned entry.identity), .ref (.interned entry.identity)], top⟩) ∨
      ∃ descriptor : String × Nat,
        source.children = List.replicate descriptor.2 (.reference (.interned entry.identity)) ∧
        source.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref (.interned entry.identity)), top⟩ := by
    intro source member
    rcases classified source member with arrowKind | ⟨descriptor, _present, related⟩
    · exact Or.inl arrowKind
    · exact Or.inr ⟨descriptor, related⟩
  obtain ⟨product, middle, productEntry, targets, bodyDone, middleValid, growth, productAvailable,
      _prepared, productRead, aligned, targetResident, _targetLive, _targetTop, _targetChildren,
      _markerMiddle, _nodeReplay⟩ :=
    SourceSynthesisUniverseMappedBodyExactFree.node_target_readback
      (literal "->") literal top entry b m bodyRows markerRow depth ordinary
      top SourceEqualityPCSNativeEdge.conjoin SourceSynthesisUniverseTopConjunction.native_conjoin_top
      initial facts cacheValid nativeUniverse nativeMarker leaf markerTop nativeKinds
      arrow arrowMember nativeArrowChildren nativeArrowKey
  have entered := SourceSynthesisUniverseSecondDomain.second_checked entry b bodyRows depth ordinary
    initial facts cacheValid nativeUniverse
  have totalGrowth : Extension initial middle := entered.2.1.trans growth
  have productNodeAvailable : Available middle.heap
      (.node productEntry (canonicalEdges targets) 0 [.intersection (pair entry.identity entry.identity).1
        (pair entry.identity entry.identity).2]) := by
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
    facts.cached.nodes probeMarkerEntry.key _ (sourceGrowth.nodeRecords _ _ probeMarkerResident)
  have probeMarkerSame : Value.node probeMarkerEntry [probeMarkerRow] 0 [] = .node m [markerRow] 0 [] :=
    SourceSynthesisUniverseMappedProbeRows.marker_eq (literal "(->)") top
      probeMarkerEntry m probeMarkerRow markerRow heap facts currentProbeMarker nativeMarker probeMarkerKey markerKey
  have sourceCurrent : ∀ row ∈ arrow :: rows, EdgeResident middle.heap row := by
    intro row member
    exact edge_grows heap middle.heap totalGrowth.heap row (sourceResident row member)
  have nativeClosed : (Value.node m [markerRow] 0 []).free = [] := rfl
  have nativeNonempty : (Value.node m [markerRow] 0 []).referenceOf ≠ .empty := by simp [Value.referenceOf]
  have probeCallbacks : ∀ ordinaryProbe : Bool,
      let probe : Reference := if ordinaryProbe then .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth) else .depth
      let target : Value Symbol Guard := if ordinaryProbe then ordinary else depth
      SourceRecursiveIntersectionMaybeMu.callback
        (.intersection (pair entry.identity entry.identity).1 (pair entry.identity entry.identity).2)
        product probe middle.heap = .done target middle.heap := by
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
    have probeCurrent : ∀ row ∈ probeArrow :: probeRows, EdgeResident middle.heap row := by
      intro row member
      exact edge_grows sourceHeap middle.heap (grows_trans sourceGrowth totalGrowth.heap)
        row (probeResident row member)
    have targetAvailable : Available heap target := by
      cases ordinaryProbe with
      | false => exact universeAvailable.children depth (by simp [InternedProbeProvenance.children])
      | true => exact universeAvailable.children ordinary (by simp [InternedProbeProvenance.children])
    have targetCurrent : Available middle.heap target := totalGrowth.available _ targetAvailable
    have replayed := mapped_product_probe literal top
      (SourceSynthesisUniverseBody.descriptors (SourceSynthesisCurrentContext.constructorCatalog lib query))
      entry.identity probe (.node m [markerRow] 0 []) arrow rows probeEntry probeArrow probeRows target
      productEntry targets middle.heap middleValid.1 nativeClosed nativeNonempty nativeArrowChildren nativeArrowKey
      catalogRows nativeProbeChildren nativeProbeKey probeAligned sourceCurrent probeCurrent probeEq productNodeAvailable
      targetCurrent bodyChildren aligned targetResident
    rw [productRead]
    exact replayed.2
  have depthCallback : SourceRecursiveIntersectionMaybeMu.callback
      (.intersection (pair entry.identity entry.identity).1 (pair entry.identity entry.identity).2)
      product .depth middle.heap = .done depth middle.heap := probeCallbacks false
  have ordinaryCallback : SourceRecursiveIntersectionMaybeMu.callback
      (.intersection (pair entry.identity entry.identity).1 (pair entry.identity entry.identity).2)
      product (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) middle.heap =
        .done ordinary middle.heap := probeCallbacks true
  have finalUniverse : Available middle.heap (.mu entry body depth ordinary) := totalGrowth.available _ universeAvailable
  obtain ⟨_keySame, table, record⟩ := available_mu_key middle.heap middleValid.1 entry body depth ordinary finalUniverse
  have kept : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
    simp [finish, cleanup, bodyEq, Value.free, Value.referenceOf]
  have pendingMember : Reference.intersection (pair entry.identity entry.identity).1
      (pair entry.identity entry.identity).2 ∈ product.free := by
    simp only [productRead, Value.free, List.mem_singleton]
  have outerDone : SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity entry.identity) product middle.heap =
      .done (.mu entry body depth ordinary) middle.heap := by
    simp only [SourceRecursiveIntersectionMaybeMu.maybeMu, ite_eq_left pendingMember,
      SourceRecursiveIntersectionMaybeMu.construct, depthCallback, Outcome.bind, ordinaryCallback,
      InternedNestedConstruction.request, table, record, kept]
  have outerNode : SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity entry.identity) product middle.heap =
      .done (.mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary) middle.heap := by
    simpa only [bodyEq, bodyRows] using outerDone
  have nativeIdentity := SourceSynthesisUniverseReferenceIdentityJoin.execute_reference_identity
    entry b m bodyRows markerRow depth ordinary top SourceEqualityPCSNativeEdge.conjoin top
    SourceSynthesisUniverseTopConjunction.native_conjoin_top initial facts cacheValid nativeUniverse nativeMarker
    leaf markerTop bodyTop bodyChildren product middle bodyDone outerNode
  have done : execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
      (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
        .done (.mu entry body depth ordinary) middle := by
    simpa only [bodyEq, bodyRows] using nativeIdentity
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := ⟨facts, cacheValid⟩
  have retainedCoverage : ∀ pending, Covered pending heap → Covered pending middle.heap := by
    intro pending incomingCovered
    exact SourceRecursiveIntersectionKernelCoverage.execute_covered (pending := pending)
      top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
      (.reference (.interned entry.identity)) (.mu entry body depth ordinary)
      initial initialValid (empty_domain initial) referenceAvailable universeAvailable incomingCovered
      (.mu entry body depth ordinary) middle done
  have retainedSemantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap heap →
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap middle.heap := by
    intro semantic
    have observed := SourceRecursiveIntersectionScopeCalls.execute_scoped
      top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
      (.reference (.interned entry.identity)) (.mu entry body depth ordinary)
      initial initialValid (empty_domain initial) referenceAvailable universeAvailable semantic
      (.mu entry body depth ordinary) middle done
    exact observed.1
  refine ⟨middle, done, middleValid, totalGrowth, finalUniverse,
    totalGrowth.available _ rootAvailable, totalGrowth.heap.nodeRecords key _ storedNow, ?_,
    retainedCoverage, retainedSemantic⟩
  intro extra
  exact (SourceRecursiveIntersectionKernel.execute_stable top SourceEqualityPCSNativeEdge.conjoin
    13 extra IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity))
    (.mu entry body depth ordinary) initial (by rw [done]; trivial)).trans done

/-- The actual current open-universe request returns the original complete Mu and exact final machine. -/
theorem current_stored_universe_reference_identity
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : heap.nodeRecords key = some (.mu entry body depth ordinary))
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (cacheValid : Cache.Valid domains) :
    let initial : Machine Symbol Guard := ⟨heap, domains⟩
    ∃ final : Machine Symbol Guard,
      execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
          .done (.mu entry body depth ordinary) final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap final.heap ∧
      Extension initial final ∧ Covered [] final.heap ∧
      Available final.heap (.mu entry body depth ordinary) ∧ Available final.heap rootValue ∧
      final.heap.nodeRecords key = some (.mu entry body depth ordinary) ∧
      (∀ extra, execute top SourceEqualityPCSNativeEdge.conjoin (13 + extra) IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
          .done (.mu entry body depth ordinary) final) := by
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have facts : Facts heap := by
    simpa only [built, Outcome.state] using checked.facts
  obtain ⟨final, done, valid, growth, universeAvailable, rootAvailable, retained, stable,
      retainedCoverage, retainedSemantic⟩ :=
    current_stored_universe_reference_identity_after_growth
      lib query signed whole accepted rootValue heap built key entry body depth ordinary stored
      heap facts (grows_refl heap) domains cacheValid
  have covered := InternedFreshOrdinaryCoverage.closed_covered (ordinarySymbols whole) rootValue heap built
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed (ordinarySymbols whole) rootValue heap built
  exact ⟨final, done, valid, retainedSemantic semantic, growth, retainedCoverage [] covered,
    universeAvailable, rootAvailable, retained, stable⟩



/-!
The following draft is uncompiled. It adds no operational definitions.
The reference alias branch uses the same source writer and stored Mu.
-/
section MixedReferenceAlias
variable {S G : Type}

private theorem mixed_pair_cancel (a b c : Nat) (same : pair a b = pair a c) : b = c := by
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair] at lower upper
  omega

private theorem mixed_pair_diagonal (a b c : Nat) (same : pair a b = pair c c) : a = c ∧ b = c := by
  have lower := congrArg Prod.fst same
  have upper := congrArg Prod.snd same
  simp only [pair, Nat.min_self, Nat.max_self] at lower upper
  omega

private theorem mixed_enter_seen (cache : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (valid : Cache.Valid cache) (source : IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : Value S G) (i j : Nat) (key : Nat × Nat) :
    key ∈ (SourceRecursiveIntersectionEnvironment.enter cache source left right i j).1.key.seen ↔
      key = pair i j ∨ key ∈ source.seen := by
  rw [SourceRecursiveIntersectionSchedule.entered_key cache valid source left right i j]
  exact SourceRecursiveIntersectionDomain.extend_seen _ _ _ _

private theorem mixed_walk_work [DecidableEq (EdgeKey S G)] {A B : Type}
    (request : A → Work S G B) (jobs : List A) (heap : State S G) :
    ∃ values finalHeap, ∀ domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey,
      walk (fun job => SourceRecursiveIntersectionKernel.work (request job)) jobs ⟨heap, domains⟩ =
        .done values ⟨finalHeap, domains⟩ := by
  induction jobs generalizing heap with
  | nil => exact ⟨[], heap, fun _ => rfl⟩
  | cons job rest ih =>
      let made := run (request job) heap
      obtain ⟨values, finalHeap, tail⟩ := ih made.2
      refine ⟨made.1 :: values, finalHeap, ?_⟩
      intro domains
      simp only [walk, SourceRecursiveIntersectionKernel.work, Result.bind]
      change (walk (fun job => SourceRecursiveIntersectionKernel.work (request job)) rest
        ⟨made.2, domains⟩).bind (fun values final => .done (made.1 :: values) final) = _
      rw [tail domains]
      rfl

private theorem mixed_walk_congr {A B : Type}
    (first second : A → Machine S G → Result S G B) (jobs : List A)
    (agree : ∀ job ∈ jobs, ∀ state, first job state = second job state) (state : Machine S G) :
    walk first jobs state = walk second jobs state := by
  induction jobs generalizing state with
  | nil => rfl
  | cons job rest ih =>
      simp only [walk, agree job List.mem_cons_self state]
      congr 1
      funext value after
      rw [ih (fun next member => agree next (List.mem_cons_of_mem _ member)) after]

private theorem mixed_body_uniform [DecidableEq S] [DecidableEq (EdgeKey S G)]
    (top : G) (conjoin : G → G → G) (conjoinTop : conjoin top top = top)
    (u : Nat) (m : Interned NodeKey) (markerRows rows : List (EdgeValue S G))
    (bodyTop : ∀ row ∈ rows, row.entry.key.constraint = top)
    (shapes : ∀ row ∈ rows,
      row.children = [.node m markerRows 0 [], .reference (.interned u), .reference (.interned u)] ∨
        ∃ arity, row.children = List.replicate arity (.reference (.interned u)))
    (functional : ∀ left ∈ rows, ∀ right ∈ rows,
      left.entry.key.symbol = right.entry.key.symbol → left.children.length = right.children.length →
        left.children = right.children)
    (heap : State S G) :
    ∃ product finalHeap, ∀ (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
      pair u u ∈ domain.key.seen → ∀ domains,
      node top conjoin (execute top conjoin 8 domain) rows rows ⟨heap, domains⟩ =
        .done product ⟨finalHeap, domains⟩ := by
  let request := fun job : EdgeValue S G × EdgeValue S G =>
    if job.1.children.length = job.2.children.length then
      makeEdge job.1.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children u job.1)
    else makeEdge job.1.entry.key.symbol top [.empty]
  obtain ⟨products, afterEdges, walked⟩ := mixed_walk_work request (pairs rows rows) heap
  let made := run (makeNode products) afterEdges
  refine ⟨made.1, made.2, ?_⟩
  intro domain seen domains
  have rowEq : ∀ job ∈ pairs rows rows, ∀ current,
      edge top conjoin (execute top conjoin 8 domain) job.1 job.2 current =
        SourceRecursiveIntersectionKernel.work (request job) current := by
    intro job member current
    obtain ⟨first, second, equalSymbols⟩ := (pairs_member rows rows job).mp member
    by_cases arity : job.1.children.length = job.2.children.length
    · have same := functional job.1 first job.2 second equalSymbols arity
      have self : edge top conjoin (execute top conjoin 8 domain) job.1 job.2 current =
          edge top conjoin (execute top conjoin 8 domain) job.1 job.1 current := by
        simp only [edge, same, bodyTop job.1 first, bodyTop job.2 second]
      rw [self, SourceSynthesisUniverseRowTransform.edge_self_work top top conjoin conjoinTop
        domain u m markerRows 0 job.1 current (bodyTop job.1 first) seen (shapes job.1 first)]
      simp only [request, arity, ite_true]
    · simp only [edge, request, arity, ite_false]
  have sameWalk := mixed_walk_congr
    (fun job : EdgeValue S G × EdgeValue S G => edge top conjoin (execute top conjoin 8 domain) job.1 job.2)
    (fun job => SourceRecursiveIntersectionKernel.work (request job))
    (pairs rows rows) rowEq ⟨heap, domains⟩
  simp only [node, sameWalk, walked domains, Result.bind, SourceRecursiveIntersectionKernel.work]
  rfl

private theorem mixed_reference_spine [DecidableEq S] [DecidableEq (EdgeKey S G)]
    (emptyGuard : G) (conjoin : G → G → G)
    (u b : Interned NodeKey) (rows : List (EdgeValue S G)) (depth ordinary : Value S G)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : Machine S G)
    (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (available : Available state.heap (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary))
    (diagonalFresh : pair u.identity u.identity ∉ domain.key.seen)
    (bodyFresh : pair b.identity u.identity ∉ domain.key.seen)
    (bodyDiagonalFresh : pair b.identity b.identity ∉ domain.key.seen) :
    let universeValue : Value S G := .mu u (.node b rows 0 [.interned u.identity]) depth ordinary
    let sourceBody : Value S G := .node b rows 0 [.interned u.identity]
    let reference : Value S G := .reference (.interned u.identity)
    let first := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key
      universeValue reference u.identity u.identity
    let second := SourceRecursiveIntersectionEnvironment.enter first.2 first.1.key
      sourceBody universeValue b.identity u.identity
    execute emptyGuard conjoin 13 domain reference universeValue state =
      ((node emptyGuard conjoin (execute emptyGuard conjoin 8 second.1)
        rows rows {state with domains := second.2}).bind
        (fun product after => construction
          (SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity u.identity) product after.heap) after)).bind
        (fun product after => construction
          (SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity) product after.heap) after) := by
  dsimp only
  let universeValue : Value S G := .mu u (.node b rows 0 [.interned u.identity]) depth ordinary
  let sourceBody : Value S G := .node b rows 0 [.interned u.identity]
  let referenceValue : Value S G := .reference (.interned u.identity)
  let first := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key
    universeValue referenceValue u.identity u.identity
  let second := SourceRecursiveIntersectionEnvironment.enter first.2 first.1.key
    sourceBody universeValue b.identity u.identity
  have different := SourceSynthesisUniverseBodyReferenceControl.body_identity_ne
    u b rows depth ordinary state facts available
  have firstValid : Cache.Valid first.2 := (IntersectionEmptyDomain.make_correct state.domains valid _).1
  have firstSeen := mixed_enter_seen state.domains valid domain.key universeValue referenceValue
    u.identity u.identity
  have secondSeen := mixed_enter_seen first.2 firstValid first.1.key sourceBody universeValue b.identity u.identity
  have firstFresh : pair b.identity u.identity ∉ first.1.key.seen := by
    intro member
    rcases (firstSeen _).mp member with same | old
    · exact different (mixed_pair_diagonal _ _ _ same).1
    · exact bodyFresh old
  have secondFresh : pair b.identity b.identity ∉ second.1.key.seen := by
    intro member
    rcases (secondSeen _).mp member with same | old
    · exact different (mixed_pair_diagonal _ _ _ same.symm).2.symm
    · rcases (firstSeen _).mp old with same | old
      · exact different (mixed_pair_diagonal _ _ _ same).1
      · exact bodyDiagonalFresh old
  have tag12 : compare (1 : Nat) 2 = .lt := by decide
  have tag14 : compare (1 : Nat) 4 = .lt := by decide
  have tag24 : compare (2 : Nat) 4 = .lt := by decide
  have tag42 : compare (4 : Nat) 2 = .gt := by decide
  have swap : decision domain.key referenceValue universeValue = .swap := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag,
      Value.referenceOf, Value.free, referenceValue, universeValue, tag42]
  have muBranch : decision domain.key universeValue referenceValue = .leftMu := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, referenceValue, universeValue, diagonalFresh, tag24]
  have refBranch : decision first.1.key sourceBody referenceValue = .rightReference := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, referenceValue, sourceBody, firstFresh, tag14]
  have bodyMuBranch : decision first.1.key sourceBody universeValue = .rightMu := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, universeValue, sourceBody, firstFresh, tag12]
  have ordinaryBranch : decision second.1.key sourceBody sourceBody = .ordinary := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, sourceBody, secondFresh]
  have firstKey := SourceRecursiveIntersectionSchedule.entered_key state.domains valid domain.key
    universeValue referenceValue u.identity u.identity
  have bound : u.identity ∈ SourceRecursiveIntersectionDomain.names first.1.key := by
    rw [firstKey]
    apply (SourceRecursiveIntersectionDomain.extend_names _ _ _ _).mpr
    left
    simp [SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
      universeValue, referenceValue]
  have read := SourcePreparedSharedRows.read_identity state.heap facts universeValue available u.identity rfl
  change execute emptyGuard conjoin 13 domain referenceValue universeValue state = _
  rw [execute]
  simp only [onNode, swap]
  change execute emptyGuard conjoin 12 domain universeValue referenceValue state = _
  rw [execute]
  simp only [onNode, muBranch]
  change (execute emptyGuard conjoin 11 first.1 sourceBody referenceValue
      {state with domains := first.2}).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity) value after.heap) after) = _
  rw [execute]
  simp only [onNode, refBranch]
  change (SourceRecursiveIntersectionKernel.reference (execute emptyGuard conjoin 10) first.1
    u.identity sourceBody false {state with domains := first.2}).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity) value after.heap) after) = _
  simp only [SourceRecursiveIntersectionKernel.reference, bound, ite_true, read, Bool.false_eq_true,
    ite_false]
  rw [execute]
  simp only [onNode, bodyMuBranch]
  change ((execute emptyGuard conjoin 9 second.1 sourceBody sourceBody
      {state with domains := second.2}).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity u.identity) value after.heap) after)).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity) value after.heap) after) = _
  rw [execute]
  simp only [onNode, ordinaryBranch]
  rfl
end MixedReferenceAlias

private theorem mixed_current_descriptor_separate (lib : Library) (query : Query)
    (descriptor : String × Nat)
    (member : descriptor ∈ SourceSynthesisUniverseBody.descriptors
      (SourceSynthesisCurrentContext.constructorCatalog lib query)) : descriptor.1 ≠ "->" := by
  rcases (List.mem_append.mp member) with rigid | catalog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at rigid
    rcases rigid with rfl | rfl | rfl | rfl <;> decide
  · exact (SourceSynthesisCurrentContext.constructorCatalog_separate lib query descriptor catalog).2.1

/-- The reference alias returns the same original Mu in the actual mixed source domain. -/
theorem current_stored_universe_reference_alias_after_mixed_entry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (patternAvailable : Available heap pattern) (patternClosed : pattern.free = [])
    (patternIdentity : SourceRecursiveIntersectionControl.identity pattern = some patternId)
    (patternShape : SourceRecursiveIntersectionControl.tag pattern = 1 ∨
      SourceRecursiveIntersectionControl.tag pattern = 3) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∃ (bound : Nat) (final : Machine Symbol Guard),
      (∀ extra, execute top SourceEqualityPCSNativeEdge.conjoin (bound + extra) entered.1
        (.reference (.interned entry.identity)) universeValue initial = .done universeValue final) ∧
      SourceRecursiveIntersectionKernel.Valid final ∧ Extension initial final := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have referenceAvailable : Available heap (.reference (.interned entry.identity)) :=
    reference_available_mu heap facts entry body depth ordinary universeAvailable
  have bodyReplay := SourceSynthesisCurrentUniverseOwnership.current_stored_universe_body_replay
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored heap growth
  obtain ⟨b, marker, arrow, rows, finalBody, calledBody, markerRead, arrowChildren, arrowKey,
      catalogRows, _bodyFacts, _bodyAvailable, _sourceResident, _markerClosed, _markerAvailable,
      coarseKinds, _arrowMember⟩ :=
    SourceSynthesisCurrentUniverseBody.current_types_callback_rows
      lib query (.interned entry.identity) heap facts referenceAvailable
  have sameBody := Outcome.done.inj (calledBody.symm.trans bodyReplay)
  have heapSame : finalBody = heap := sameBody.2
  subst finalBody
  have bodyEq : body = .node b (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity] := sameBody.1.symm
  let bodyRows := canonicalEdges (arrow :: rows)
  obtain ⟨m, markerRow, markerEq, _leaf, _markerKey⟩ := markerRead
  have nativeUniverse : Available heap
      (.mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    simpa only [universeValue, bodyEq, bodyRows] using universeAvailable
  have nativeArrowChildren : arrow.children = [.node m [markerRow] 0 [],
      .reference (.interned entry.identity), .reference (.interned entry.identity)] := by
    simpa only [markerEq] using arrowChildren
  have nativeArrowKey : arrow.entry.key = ⟨literal "->", [(Value.node m [markerRow] 0 []).referenceOf,
      .ref (.interned entry.identity), .ref (.interned entry.identity)], top⟩ := by
    simpa only [markerEq] using arrowKey
  have classified := SourceSynthesisUniverseMappedBodyCanonical.canonical_row_kinds
    (literal "->") literal top entry.identity (.node m [markerRow] 0 []) arrow
    (SourceSynthesisUniverseBody.descriptors (SourceSynthesisCurrentContext.constructorCatalog lib query)) rows
    nativeArrowChildren nativeArrowKey catalogRows
  have bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top :=
    fun row member => (coarseKinds row member).1
  have shapes : ∀ row ∈ bodyRows,
      row.children = [.node m [markerRow] 0 [], .reference (.interned entry.identity),
        .reference (.interned entry.identity)] ∨
      ∃ arity, row.children = List.replicate arity (.reference (.interned entry.identity)) := by
    intro row member
    rcases classified row member with arrowKind | ⟨descriptor, _present, related⟩
    · exact Or.inl arrowKind.1
    · exact Or.inr ⟨descriptor.2, related.1⟩
  have functional : ∀ left ∈ bodyRows, ∀ right ∈ bodyRows,
      left.entry.key.symbol = right.entry.key.symbol → left.children.length = right.children.length →
      left.children = right.children := by
    intro left leftIn right rightIn sameSymbol sameArity
    rcases classified left leftIn with leftArrow | ⟨leftDescriptor, leftIn, leftCatalog⟩ <;>
      rcases classified right rightIn with rightArrow | ⟨rightDescriptor, rightIn, rightCatalog⟩
    · exact leftArrow.1.trans rightArrow.1.symm
    · have names : "->" = rightDescriptor.1 := by
        have symbols := sameSymbol
        rw [leftArrow.2, rightCatalog.2] at symbols
        exact congrArg Prod.fst symbols
      exact False.elim ((mixed_current_descriptor_separate lib query rightDescriptor rightIn) names.symm)
    · have names : leftDescriptor.1 = "->" := by
        have symbols := sameSymbol
        rw [leftCatalog.2, rightArrow.2] at symbols
        exact congrArg Prod.fst symbols
      exact False.elim ((mixed_current_descriptor_separate lib query leftDescriptor leftIn) names)
    · have arities : leftDescriptor.2 = rightDescriptor.2 := by
        simpa only [leftCatalog.1, rightCatalog.1, List.length_replicate] using sameArity
      rw [leftCatalog.1, rightCatalog.1, arities]
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  have mixedChecked := SourceRecursiveIntersectionKernel.entered
    (⟨heap, domains⟩ : Machine Symbol Guard) ⟨facts, cacheValid⟩
    IntersectionEmptyDomain.emptyDomain (empty_domain _) universeValue pattern universeAvailable patternAvailable
    entry.identity patternId
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := mixedChecked.1
  have initialKnown : SourceRecursiveIntersectionKernel.Domain initial entered.1 := mixedChecked.2.2
  have bAvailable : Available heap (.node b bodyRows 0 [.interned entry.identity]) :=
    nativeUniverse.children _ (by simp [InternedProbeProvenance.children])
  have bNeU := SourceSynthesisUniverseBodyReferenceControl.body_identity_ne
    entry b bodyRows depth ordinary initial facts nativeUniverse
  have patternReference : SourcePreparedSharedRows.reference pattern = some patternId := by
    cases pattern with
    | empty =>
        change (none : Option Nat) = some patternId at patternIdentity
        cases patternIdentity
    | reference name =>
        change (4 : Nat) = 1 ∨ 4 = 3 at patternShape
        omega
    | node other otherRows otherDepth otherFree => exact patternIdentity
    | mu other otherBody otherDepth otherOrdinary =>
        change (2 : Nat) = 1 ∨ 2 = 3 at patternShape
        omega
    | union other members otherDepth otherFree => exact patternIdentity
  have patternRead := SourcePreparedSharedRows.read_identity heap facts pattern patternAvailable patternId patternReference
  have universeRead := SourcePreparedSharedRows.read_identity heap facts universeValue universeAvailable entry.identity rfl
  have bodyRead := SourcePreparedSharedRows.read_identity heap facts
    (.node b bodyRows 0 [.interned entry.identity]) bAvailable b.identity rfl
  have pNeU : patternId ≠ entry.identity := by
    intro same
    rw [same] at patternRead
    have values : pattern = universeValue := Option.some.inj (patternRead.symm.trans universeRead)
    rw [values] at patternShape
    rcases patternShape with bad | bad <;> simp [universeValue, tag] at bad
  have pNeB : patternId ≠ b.identity := by
    intro same
    rw [same] at patternRead
    have values : pattern = .node b bodyRows 0 [.interned entry.identity] :=
      Option.some.inj (patternRead.symm.trans bodyRead)
    have free := congrArg Value.free values
    rw [patternClosed] at free
    cases free
  have enteredSeen : ∀ name, name ∈ entered.1.key.seen ↔ name = pair entry.identity patternId := by
    intro name
    change name ∈ (SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId).1.key.seen ↔ name = pair entry.identity patternId
    simpa only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil, or_false] using
      mixed_enter_seen domains cacheValid IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId name
  have diagonalFresh : pair entry.identity entry.identity ∉ entered.1.key.seen := by
    intro member
    have same := (enteredSeen _).mp member
    exact pNeU (mixed_pair_cancel _ _ _ same).symm
  have bodyFresh : pair b.identity entry.identity ∉ entered.1.key.seen := by
    intro member
    have same : pair entry.identity b.identity = pair entry.identity patternId := by
      simpa only [pair, Nat.min_comm, Nat.max_comm] using (enteredSeen _).mp member
    exact pNeB (mixed_pair_cancel _ _ _ same).symm
  have bodyDiagonalFresh : pair b.identity b.identity ∉ entered.1.key.seen := by
    intro member
    have same := (enteredSeen _).mp member
    exact bNeU (mixed_pair_diagonal _ _ _ same.symm).1.symm
  let nativeU : Value Symbol Guard := .mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary
  let nativeB : Value Symbol Guard := .node b bodyRows 0 [.interned entry.identity]
  let nativeR : Value Symbol Guard := .reference (.interned entry.identity)
  let actualFirst := SourceRecursiveIntersectionEnvironment.enter initial.domains entered.1.key
    nativeU nativeR entry.identity entry.identity
  let actualSecond := SourceRecursiveIntersectionEnvironment.enter actualFirst.2 actualFirst.1.key
    nativeB nativeU b.identity entry.identity
  let standardFirst := SourceRecursiveIntersectionEnvironment.enter initial.domains IntersectionEmptyDomain.emptyKey
    nativeU nativeR entry.identity entry.identity
  let standardSecond := SourceRecursiveIntersectionEnvironment.enter standardFirst.2 standardFirst.1.key
    nativeB nativeU b.identity entry.identity
  have actualFirstValid : Cache.Valid actualFirst.2 :=
    (IntersectionEmptyDomain.make_correct initial.domains initialValid.2 _).1
  have standardFirstValid : Cache.Valid standardFirst.2 :=
    (IntersectionEmptyDomain.make_correct initial.domains initialValid.2 _).1
  have actualDiag : pair entry.identity entry.identity ∈ actualSecond.1.key.seen := by
    apply (mixed_enter_seen actualFirst.2 actualFirstValid actualFirst.1.key
      nativeB nativeU b.identity entry.identity _).mpr
    right
    exact (mixed_enter_seen initial.domains initialValid.2 entered.1.key
      nativeU nativeR entry.identity entry.identity _).mpr (Or.inl rfl)
  have standardDiag : pair entry.identity entry.identity ∈ standardSecond.1.key.seen := by
    apply (mixed_enter_seen standardFirst.2 standardFirstValid standardFirst.1.key
      nativeB nativeU b.identity entry.identity _).mpr
    right
    exact (mixed_enter_seen initial.domains initialValid.2 IntersectionEmptyDomain.emptyKey
      nativeU nativeR entry.identity entry.identity _).mpr (Or.inl rfl)
  obtain ⟨product, productHeap, bodyUniform⟩ := mixed_body_uniform top SourceEqualityPCSNativeEdge.conjoin
    SourceSynthesisUniverseTopConjunction.native_conjoin_top entry.identity m [markerRow] bodyRows
    bodyTop shapes functional heap
  have actualBody := bodyUniform actualSecond.1 actualDiag actualSecond.2
  have standardBody := bodyUniform standardSecond.1 standardDiag standardSecond.2
  obtain ⟨standardFinal, standardDone, _rest⟩ := current_stored_universe_reference_identity_after_growth
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    heap facts growth initial.domains initialValid.2
  have actualSpine := mixed_reference_spine top SourceEqualityPCSNativeEdge.conjoin entry b bodyRows depth ordinary
    entered.1 initial facts initialValid.2 nativeUniverse diagonalFresh bodyFresh bodyDiagonalFresh
  have standardSpine := mixed_reference_spine top SourceEqualityPCSNativeEdge.conjoin entry b bodyRows depth ordinary
    IntersectionEmptyDomain.emptyDomain initial facts initialValid.2 nativeUniverse
    (by simp [IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey])
    (by simp [IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey])
    (by simp [IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey])
  have nativeEq : universeValue = nativeU := by
    change Value.mu entry body depth ordinary =
      Value.mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary
    rw [bodyEq]
  change execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
    nativeR universeValue initial = .done universeValue standardFinal at standardDone
  rw [nativeEq] at standardDone
  have observed := standardSpine.symm.trans standardDone
  change ((node top SourceEqualityPCSNativeEdge.conjoin
      (execute top SourceEqualityPCSNativeEdge.conjoin 8 standardSecond.1) bodyRows bodyRows
      (⟨heap, standardSecond.2⟩ : Machine Symbol Guard)).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity entry.identity) value after.heap) after)).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity entry.identity) value after.heap) after) =
    .done nativeU standardFinal at observed
  rw [standardBody] at observed
  simp only [Result.bind] at observed
  have actualReduced := actualSpine
  change execute top SourceEqualityPCSNativeEdge.conjoin 13 entered.1 nativeR nativeU initial =
    ((node top SourceEqualityPCSNativeEdge.conjoin
      (execute top SourceEqualityPCSNativeEdge.conjoin 8 actualSecond.1) bodyRows bodyRows
      (⟨heap, actualSecond.2⟩ : Machine Symbol Guard)).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity entry.identity) value after.heap) after)).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity entry.identity) value after.heap) after)
    at actualReduced
  rw [actualBody] at actualReduced
  simp only [Result.bind] at actualReduced
  let final : Machine Symbol Guard := ⟨standardFinal.heap, actualSecond.2⟩
  have nativeDone : execute top SourceEqualityPCSNativeEdge.conjoin 13 entered.1 nativeR nativeU initial =
      .done nativeU final := by
    rw [actualReduced]
    cases firstOutcome : SourceRecursiveIntersectionMaybeMu.maybeMu
        (pair b.identity entry.identity) product productHeap with
    | pending pending after =>
        simp only [firstOutcome, construction] at observed
        cases observed
    | done inner after =>
        simp only [firstOutcome, construction] at observed ⊢
        cases lastOutcome : SourceRecursiveIntersectionMaybeMu.maybeMu
            (pair entry.identity entry.identity) inner after with
        | pending pending after =>
            simp only [lastOutcome] at observed
            cases observed
        | done output finalHeap =>
            simp only [lastOutcome] at observed ⊢
            obtain ⟨valueSame, stateSame⟩ := Result.done.inj observed
            have heapSame := congrArg Machine.heap stateSame
            change finalHeap = standardFinal.heap at heapSame
            simp only [valueSame, final, heapSame]
  have done : execute top SourceEqualityPCSNativeEdge.conjoin 13 entered.1
      (.reference (.interned entry.identity)) universeValue initial = .done universeValue final := by
    simpa only [nativeEq, nativeR] using nativeDone
  have checked := execute_checked top SourceEqualityPCSNativeEdge.conjoin 13 entered.1
    (.reference (.interned entry.identity)) universeValue initial initialValid initialKnown
    referenceAvailable universeAvailable
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := by
    simpa only [done, Result.state] using checked.valid
  have finalGrowth : Extension initial final := by
    simpa only [done, Result.state] using checked.extension
  refine ⟨13, final, ?_, finalValid, finalGrowth⟩
  intro extra
  exact (execute_stable top SourceEqualityPCSNativeEdge.conjoin 13 extra entered.1
    (.reference (.interned entry.identity)) universeValue initial (by rw [done]; trivial)).trans done

section MixedBodyProbe
variable {S G : Type}

private theorem mixed_rows_probe_at [DecidableEq (EdgeKey S G)]
    (top : G) (owner : Nat) (cutoff probe : Reference) (marker : Value S G)
    (originals products targets : List (EdgeValue S G)) (current : State S G)
    (closed : marker.free = [])
    (kinds : ∀ original ∈ originals, ∀ child ∈ original.children,
      child = marker ∨ child = .reference (.interned owner))
    (readback : All₂ (fun (source : EdgeValue S G) product =>
      product.children = source.children.map (input (replacement (.interned owner) (.reference cutoff))) ∧
      product.entry.key = ⟨source.entry.key.symbol,
        (source.children.map (input (replacement (.interned owner) (.reference cutoff)))).map Value.referenceOf,
        top⟩) originals products)
    (replayed : All₂ (fun original target =>
      run (makeEdge original.entry.key.symbol top
        (original.children.map (input (replacement (.interned owner) (.reference probe))))) current =
          (target, current)) originals targets) :
    All₂ (fun product target =>
      run (makeEdge product.entry.key.symbol top
        (product.children.map (input (replacement cutoff (.reference probe))))) current =
          (target, current)) products targets := by
  revert kinds replayed
  induction readback generalizing targets with
  | nil => intro _ replayed; cases replayed; exact .nil
  | @cons original product originals products own rest ih =>
      intro kinds replayed
      cases replayed with
      | @cons _ target _ targets first tail =>
          refine .cons ?_ (ih targets
            (fun original member => kinds original (List.mem_cons_of_mem _ member)) tail)
          have projected := congrArg EdgeKey.symbol own.2
          have symbol : product.entry.key.symbol = original.entry.key.symbol := projected
          have composed : product.children.map (input (replacement cutoff (.reference probe))) =
              original.children.map (input (replacement (.interned owner) (.reference probe))) := by
            rw [own.1, List.map_map]
            apply List.map_congr_left
            intro child member
            apply SourceSynthesisUniverseProbeCutoffComposition.input_compose_at owner cutoff probe child
            rcases kinds original List.mem_cons_self child member with same | same
            · left
              rw [same]
              exact closed
            · exact Or.inr same
          rw [symbol, composed]
          exact first

private theorem mixed_product_probe_at [DecidableEq (EdgeKey S G)]
    (makeLiteral : String → S) (top : G) (catalog : List (String × Nat))
    (owner : Nat) (cutoff probe : Reference) (marker : Value S G)
    (sourceArrow : EdgeValue S G) (sources : List (EdgeValue S G))
    (targetEntry : Interned NodeKey) (targetArrow : EdgeValue S G)
    (targets : List (EdgeValue S G)) (target : Value S G)
    (productEntry : Interned NodeKey) (products : List (EdgeValue S G))
    (current : State S G) (facts : Facts current)
    (closed : marker.free = []) (nonemptyMarker : marker.referenceOf ≠ .empty)
    (sourceChildren : sourceArrow.children = [marker, .reference (.interned owner), .reference (.interned owner)])
    (sourceKey : sourceArrow.entry.key =
      ⟨makeLiteral "->", [marker.referenceOf, .ref (.interned owner), .ref (.interned owner)], top⟩)
    (sourceAligned : All₂ (fun (descriptor : String × Nat) (row : EdgeValue S G) =>
      row.children = List.replicate descriptor.2 (.reference (.interned owner)) ∧
      row.entry.key = ⟨makeLiteral descriptor.1, List.replicate descriptor.2 (.ref (.interned owner)), top⟩) catalog sources)
    (targetChildren : targetArrow.children = [marker, .reference probe, .reference probe])
    (targetKey : targetArrow.entry.key = ⟨makeLiteral "->", [marker.referenceOf, .ref probe, .ref probe], top⟩)
    (targetAligned : All₂ (fun (descriptor : String × Nat) (row : EdgeValue S G) =>
      row.children = List.replicate descriptor.2 (.reference probe) ∧
      row.entry.key = ⟨makeLiteral descriptor.1, List.replicate descriptor.2 (.ref probe), top⟩) catalog targets)
    (sourceResident : ∀ row ∈ sourceArrow :: sources, EdgeResident current row)
    (targetResident : ∀ row ∈ targetArrow :: targets, EdgeResident current row)
    (targetEq : target = .node targetEntry (canonicalEdges (targetArrow :: targets)) 0 [probe])
    (productAvailable : Available current (.node productEntry (canonicalEdges products) 0 [cutoff]))
    (targetAvailable : Available current target)
    (sourceKinds : ∀ row ∈ canonicalEdges (sourceArrow :: sources), ∀ child ∈ row.children,
      child = marker ∨ child = .reference (.interned owner))
    (readback : All₂ (fun (source : EdgeValue S G) product =>
      product.children = source.children.map (input (replacement (.interned owner) (.reference cutoff))) ∧
      product.entry.key = ⟨source.entry.key.symbol,
        (source.children.map (input (replacement (.interned owner) (.reference cutoff)))).map Value.referenceOf,
        top⟩) (canonicalEdges (sourceArrow :: sources)) products)
    (productResident : ∀ row ∈ products, EdgeResident current row) :
    InternedFreshOrdinaryStoredSubstitution.execute
      (.node productEntry (canonicalEdges products) 0 [cutoff])
      (replacement cutoff (.reference probe)) current = .done target current ∧
    SourceRecursiveIntersectionMaybeMu.callback cutoff
      (.node productEntry (canonicalEdges products) 0 [cutoff]) probe current = .done target current := by
  have replayed := SourceSynthesisUniverseMappedProbeRows.raw_rows_replay makeLiteral top (.interned owner) probe marker
    sourceArrow targetArrow catalog sources targets current facts closed sourceChildren sourceKey targetKey
    sourceAligned targetAligned targetResident
  obtain ⟨canonicalTargets, canonicalReplay, _members, canonicalResident, sameNode⟩ :=
    SourceSynthesisUniverseCanonicalRowReplay.canonical_replay top
      (replacement (.interned owner) (.reference probe)) (sourceArrow :: sources) (targetArrow :: targets)
      current facts sourceResident targetResident replayed
  have targetLive : ∀ row ∈ targetArrow :: targets,
      row.children.any (fun child => child.referenceOf == .empty) = false := by
    have catalogLive : ∀ row ∈ targets,
        row.children.any (fun child => child.referenceOf == .empty) = false := by
      intro row member
      obtain ⟨descriptor, _included, related⟩ := aligned_output targetAligned row member
      simp [related.1, Value.referenceOf]
    intro row member
    rcases List.mem_cons.mp member with rfl | later
    · simp [targetChildren, Value.referenceOf]
      exact nonemptyMarker
    · exact catalogLive row later
  have survivingTargets : surviving (targetArrow :: targets) = targetArrow :: targets := by
    unfold surviving
    apply List.filter_eq_self.mpr
    intro row member
    simp only [targetLive row member, Bool.not_false]
  have retained : targetArrow ∈ canonicalEdges (targetArrow :: targets) :=
    canonicalEdges_retains current facts.coherent _ targetArrow targetResident List.mem_cons_self
  have targetNonempty : canonicalEdges (surviving (targetArrow :: targets)) ≠ [] := by
    rw [survivingTargets]
    intro absent
    simp only [absent, List.not_mem_nil] at retained
  have targetNodeAvailable : Available current
      (.node targetEntry (canonicalEdges (surviving (targetArrow :: targets))) 0 [probe]) := by
    rw [survivingTargets, ← targetEq]
    exact targetAvailable
  have targetNode := SourceSynthesisUniverseNodeReplay.resident_node_replay
    (targetArrow :: targets) targetEntry 0 [probe] current facts targetNodeAvailable targetNonempty
  have nodeReplay : run (makeNode canonicalTargets) current = (target, current) := by
    rw [sameNode]
    simpa only [survivingTargets, ← targetEq] using targetNode
  have rowsReplay := mixed_rows_probe_at top owner cutoff probe marker
    (canonicalEdges (sourceArrow :: sources)) products canonicalTargets current closed sourceKinds readback canonicalReplay
  have fields : ∀ product ∈ products, product.entry.key.constraint = top ∧
      ∀ child ∈ product.children, child = marker ∨ child = .reference cutoff := by
    intro product member
    obtain ⟨source, sourceIn, own⟩ := aligned_output readback product member
    have guard := congrArg EdgeKey.constraint own.2
    refine ⟨guard, ?_⟩
    intro child present
    rw [own.1] at present
    obtain ⟨original, included, mapped⟩ := List.mem_map.mp present
    rcases sourceKinds source sourceIn original included with same | same
    · left
      rw [same, InternedStoredSubstitutionScope.input_closed marker _ closed] at mapped
      exact mapped.symm
    · right
      simpa [same, input, replacement] using mapped.symm
  have workDone := SourceSynthesisUniverseCanonicalRowReplay.execute_eq_work_of_raw top
    cutoff productEntry products canonicalTargets marker (replacement cutoff (.reference probe)) current facts
    productAvailable closed productResident canonicalResident (fun row member => (fields row member).1)
    (fun row member => (fields row member).2) rowsReplay
  have done : InternedFreshOrdinaryStoredSubstitution.execute
      (.node productEntry (canonicalEdges products) 0 [cutoff]) (replacement cutoff (.reference probe)) current =
        .done target current := by
    rw [workDone]
    simp only [InternedNestedConstruction.work, nodeReplay]
  refine ⟨done, ?_⟩
  simp only [SourceRecursiveIntersectionMaybeMu.callback, done, Outcome.bind, targetEq,
    withoutSelfReference, InternedNestedConstruction.work, run]

end MixedBodyProbe

/-- The body alias returns the same original Mu in the actual mixed source domain. -/
theorem current_stored_universe_body_alias_after_mixed_entry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (patternAvailable : Available heap pattern) (patternClosed : pattern.free = [])
    (patternIdentity : SourceRecursiveIntersectionControl.identity pattern = some patternId)
    (patternShape : SourceRecursiveIntersectionControl.tag pattern = 1 ∨
      SourceRecursiveIntersectionControl.tag pattern = 3) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∃ (bound : Nat) (final : Machine Symbol Guard),
      (∀ extra, execute top SourceEqualityPCSNativeEdge.conjoin (bound + extra) entered.1
        body universeValue initial = .done universeValue final) ∧
      SourceRecursiveIntersectionKernel.Valid final ∧ Extension initial final := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have referenceAvailable : Available heap (.reference (.interned entry.identity)) :=
    reference_available_mu heap facts entry body depth ordinary universeAvailable
  have bodyReplay := SourceSynthesisCurrentUniverseOwnership.current_stored_universe_body_replay
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored heap growth
  obtain ⟨b, marker, arrow, rows, finalBody, calledBody, markerRead, arrowChildren, arrowKey,
      catalogRows, _bodyFacts, _bodyAvailable, sourceResident, _markerClosed, markerAvailable,
      coarseKinds, arrowMember⟩ :=
    SourceSynthesisCurrentUniverseBody.current_types_callback_rows
      lib query (.interned entry.identity) heap facts referenceAvailable
  have sameBody := Outcome.done.inj (calledBody.symm.trans bodyReplay)
  have heapSame : finalBody = heap := sameBody.2
  subst finalBody
  have bodyEq : body = .node b (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity] := sameBody.1.symm
  let bodyRows := canonicalEdges (arrow :: rows)
  obtain ⟨m, markerRow, markerEq, _leaf, markerKey⟩ := markerRead
  have nativeMarker : Available heap (.node m [markerRow] 0 []) := by
    rw [← markerEq]
    exact markerAvailable
  have nativeUniverse : Available heap
      (.mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    simpa only [universeValue, bodyEq, bodyRows] using universeAvailable
  have nativeArrowChildren : arrow.children = [.node m [markerRow] 0 [],
      .reference (.interned entry.identity), .reference (.interned entry.identity)] := by
    simpa only [markerEq] using arrowChildren
  have nativeArrowKey : arrow.entry.key = ⟨literal "->", [(Value.node m [markerRow] 0 []).referenceOf,
      .ref (.interned entry.identity), .ref (.interned entry.identity)], top⟩ := by
    simpa only [markerEq] using arrowKey
  have classified := SourceSynthesisUniverseMappedBodyCanonical.canonical_row_kinds
    (literal "->") literal top entry.identity (.node m [markerRow] 0 []) arrow
    (SourceSynthesisUniverseBody.descriptors (SourceSynthesisCurrentContext.constructorCatalog lib query)) rows
    nativeArrowChildren nativeArrowKey catalogRows
  have bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top :=
    fun row member => (coarseKinds row member).1
  have bodyChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned entry.identity) := by
    intro row member child included
    simpa only [markerEq] using (coarseKinds row member).2 child included
  have functional : ∀ left ∈ bodyRows, ∀ right ∈ bodyRows,
      left.entry.key.symbol = right.entry.key.symbol → left.children.length = right.children.length →
      left.children = right.children := by
    intro left leftIn right rightIn sameSymbol sameArity
    rcases classified left leftIn with leftArrow | ⟨leftDescriptor, leftIn, leftCatalog⟩ <;>
      rcases classified right rightIn with rightArrow | ⟨rightDescriptor, rightIn, rightCatalog⟩
    · exact leftArrow.1.trans rightArrow.1.symm
    · have names : "->" = rightDescriptor.1 := by
        have symbols := sameSymbol
        rw [leftArrow.2, rightCatalog.2] at symbols
        exact congrArg Prod.fst symbols
      exact False.elim ((mixed_current_descriptor_separate lib query rightDescriptor rightIn) names.symm)
    · have names : leftDescriptor.1 = "->" := by
        have symbols := sameSymbol
        rw [leftCatalog.2, rightArrow.2] at symbols
        exact congrArg Prod.fst symbols
      exact False.elim ((mixed_current_descriptor_separate lib query leftDescriptor leftIn) names)
    · have arities : leftDescriptor.2 = rightDescriptor.2 := by
        simpa only [leftCatalog.1, rightCatalog.1, List.length_replicate] using sameArity
      rw [leftCatalog.1, rightCatalog.1, arities]
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  have mixedChecked := SourceRecursiveIntersectionKernel.entered
    (⟨heap, domains⟩ : Machine Symbol Guard) ⟨facts, cacheValid⟩
    IntersectionEmptyDomain.emptyDomain (empty_domain _) universeValue pattern universeAvailable patternAvailable
    entry.identity patternId
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := mixedChecked.1
  have initialKnown : SourceRecursiveIntersectionKernel.Domain initial entered.1 := mixedChecked.2.2
  have bAvailable : Available heap (.node b bodyRows 0 [.interned entry.identity]) :=
    nativeUniverse.children _ (by simp [InternedProbeProvenance.children])
  have bNeU := SourceSynthesisUniverseBodyReferenceControl.body_identity_ne
    entry b bodyRows depth ordinary initial facts nativeUniverse
  have patternReference : SourcePreparedSharedRows.reference pattern = some patternId := by
    cases pattern with
    | empty =>
        change (none : Option Nat) = some patternId at patternIdentity
        cases patternIdentity
    | reference name =>
        change (4 : Nat) = 1 ∨ 4 = 3 at patternShape
        omega
    | node other otherRows otherDepth otherFree => exact patternIdentity
    | mu other otherBody otherDepth otherOrdinary =>
        change (2 : Nat) = 1 ∨ 2 = 3 at patternShape
        omega
    | union other members otherDepth otherFree => exact patternIdentity
  have patternRead := SourcePreparedSharedRows.read_identity heap facts pattern patternAvailable patternId patternReference
  have universeRead := SourcePreparedSharedRows.read_identity heap facts universeValue universeAvailable entry.identity rfl
  have bodyRead := SourcePreparedSharedRows.read_identity heap facts
    (.node b bodyRows 0 [.interned entry.identity]) bAvailable b.identity rfl
  have pNeU : patternId ≠ entry.identity := by
    intro same
    rw [same] at patternRead
    have values : pattern = universeValue := Option.some.inj (patternRead.symm.trans universeRead)
    rw [values] at patternShape
    rcases patternShape with bad | bad <;> simp [universeValue, tag] at bad
  have pNeB : patternId ≠ b.identity := by
    intro same
    rw [same] at patternRead
    have values : pattern = .node b bodyRows 0 [.interned entry.identity] :=
      Option.some.inj (patternRead.symm.trans bodyRead)
    have free := congrArg Value.free values
    rw [patternClosed] at free
    cases free
  have enteredSeen : ∀ name, name ∈ entered.1.key.seen ↔ name = pair entry.identity patternId := by
    intro name
    change name ∈ (SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId).1.key.seen ↔ name = pair entry.identity patternId
    simpa only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil, or_false] using
      mixed_enter_seen domains cacheValid IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId name
  have diagonalFresh : pair entry.identity entry.identity ∉ entered.1.key.seen := by
    intro member
    have same := (enteredSeen _).mp member
    exact pNeU (mixed_pair_cancel _ _ _ same).symm
  have bodyFresh : pair b.identity entry.identity ∉ entered.1.key.seen := by
    intro member
    have same : pair entry.identity b.identity = pair entry.identity patternId := by
      simpa only [pair, Nat.min_comm, Nat.max_comm] using (enteredSeen _).mp member
    exact pNeB (mixed_pair_cancel _ _ _ same).symm
  have bodyDiagonalFresh : pair b.identity b.identity ∉ entered.1.key.seen := by
    intro member
    have same := (enteredSeen _).mp member
    exact bNeU (mixed_pair_diagonal _ _ _ same.symm).1.symm
  let nativeU : Value Symbol Guard := .mu entry (.node b bodyRows 0 [.interned entry.identity]) depth ordinary
  let nativeB : Value Symbol Guard := .node b bodyRows 0 [.interned entry.identity]
  let bodyEntered := SourceRecursiveIntersectionEnvironment.enter initial.domains entered.1.key
    nativeB nativeU b.identity entry.identity
  let bodyInitial : Machine Symbol Guard := {initial with domains := bodyEntered.2}
  have bodyChecked := SourceRecursiveIntersectionKernel.entered initial initialValid entered.1 initialKnown
    nativeB nativeU bAvailable nativeUniverse b.identity entry.identity
  have bodyInitialValid : SourceRecursiveIntersectionKernel.Valid bodyInitial := bodyChecked.1
  have bodyInitialKnown : Domain bodyInitial bodyEntered.1 := bodyChecked.2.2
  have bodyEntrySeen := mixed_enter_seen initial.domains initialValid.2 entered.1.key
    nativeB nativeU b.identity entry.identity
  have selectedSeen : pair b.identity entry.identity ∈ bodyEntered.1.key.seen :=
    (bodyEntrySeen _).mpr (Or.inl rfl)
  have selectedFresh : pair entry.identity entry.identity ∉ bodyEntered.1.key.seen := by
    intro member
    rcases (bodyEntrySeen _).mp member with same | old
    · exact bNeU (mixed_pair_diagonal _ _ _ same.symm).1
    · exact diagonalFresh old
  have selectedBodyFresh : pair b.identity b.identity ∉ bodyEntered.1.key.seen := by
    intro member
    rcases (bodyEntrySeen _).mp member with same | old
    · exact bNeU (mixed_pair_diagonal _ _ _ same.symm).2.symm
    · exact bodyDiagonalFresh old
  have bodyEntryKey := SourceRecursiveIntersectionSchedule.entered_key initial.domains initialValid.2
    entered.1.key nativeB nativeU b.identity entry.identity
  have selectedBound : entry.identity ∈ SourceRecursiveIntersectionDomain.names bodyEntered.1.key := by
    rw [bodyEntryKey]
    apply (SourceRecursiveIntersectionDomain.extend_names _ _ _ _).mpr
    left
    simp [SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
      nativeB, nativeU]
  obtain ⟨product, middle, productEntry, targets, bodyDone, middleValid, bodyGrowth,
      productAvailable, productRead, aligned, targetResident, _targetLive, _nodeReplay⟩ :=
    SourceSynthesisUniverseOffDiagonalBody.node_target_readback top SourceEqualityPCSNativeEdge.conjoin
      SourceSynthesisUniverseTopConjunction.native_conjoin_top entry b m bodyRows [markerRow] depth ordinary
      bodyEntered.1 bodyInitial bodyInitialValid bodyInitialKnown nativeUniverse referenceAvailable nativeMarker
      selectedBound selectedSeen selectedFresh bodyTop bodyChildren functional arrow arrowMember nativeArrowChildren
  have totalGrowth : Extension initial middle := bodyChecked.2.1.trans bodyGrowth
  let cutoff : Reference := .intersection (pair b.identity entry.identity).1 (pair b.identity entry.identity).2
  have productNodeAvailable : Available middle.heap
      (.node productEntry (canonicalEdges targets) 0 [cutoff]) := by
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
  have sourceCurrent : ∀ row ∈ arrow :: rows, EdgeResident middle.heap row := by
    intro row member
    exact edge_grows heap middle.heap totalGrowth.heap row (sourceResident row member)
  have nativeClosed : (Value.node m [markerRow] 0 []).free = [] := rfl
  have nativeNonempty : (Value.node m [markerRow] 0 []).referenceOf ≠ .empty := by simp [Value.referenceOf]
  have probeCallbacks : ∀ ordinaryProbe : Bool,
      let probe : Reference := if ordinaryProbe then .uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth) else .depth
      let target : Value Symbol Guard := if ordinaryProbe then ordinary else depth
      SourceRecursiveIntersectionMaybeMu.callback cutoff product probe middle.heap = .done target middle.heap := by
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
    have probeCurrent : ∀ row ∈ probeArrow :: probeRows, EdgeResident middle.heap row := by
      intro row member
      exact edge_grows sourceHeap middle.heap (grows_trans growth totalGrowth.heap)
        row (probeResident row member)
    have targetAvailable : Available heap target := by
      cases ordinaryProbe with
      | false => exact nativeUniverse.children depth (by simp [InternedProbeProvenance.children])
      | true => exact nativeUniverse.children ordinary (by simp [InternedProbeProvenance.children])
    have targetCurrent : Available middle.heap target := totalGrowth.available _ targetAvailable
    have replayed := mixed_product_probe_at literal top
      (SourceSynthesisUniverseBody.descriptors (SourceSynthesisCurrentContext.constructorCatalog lib query))
      entry.identity cutoff probe (.node m [markerRow] 0 []) arrow rows probeEntry probeArrow probeRows target
      productEntry targets middle.heap middleValid.1 nativeClosed nativeNonempty nativeArrowChildren nativeArrowKey
      catalogRows nativeProbeChildren nativeProbeKey probeAligned sourceCurrent probeCurrent probeEq productNodeAvailable
      targetCurrent bodyChildren aligned targetResident
    rw [productRead]
    exact replayed.2
  have depthCallback : SourceRecursiveIntersectionMaybeMu.callback cutoff product .depth middle.heap =
      .done depth middle.heap := probeCallbacks false
  have ordinaryCallback : SourceRecursiveIntersectionMaybeMu.callback cutoff product
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) middle.heap =
        .done ordinary middle.heap := probeCallbacks true
  dsimp only [cutoff] at depthCallback ordinaryCallback
  have finalUniverse : Available middle.heap (.mu entry body depth ordinary) := totalGrowth.available _ universeAvailable
  obtain ⟨_keySame, table, record⟩ := available_mu_key middle.heap middleValid.1 entry body depth ordinary finalUniverse
  have kept : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
    simp [finish, cleanup, bodyEq, Value.free, Value.referenceOf]
  have pendingMember : Reference.intersection (pair b.identity entry.identity).1
      (pair b.identity entry.identity).2 ∈ product.free := by
    simp only [productRead, Value.free, List.mem_singleton]
  have outerDone : SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity entry.identity) product middle.heap =
      .done (.mu entry body depth ordinary) middle.heap := by
    simp only [SourceRecursiveIntersectionMaybeMu.maybeMu, ite_eq_left pendingMember,
      SourceRecursiveIntersectionMaybeMu.construct, depthCallback, Outcome.bind, ordinaryCallback,
      InternedNestedConstruction.request, table, record, kept]
  have outerNode : SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity entry.identity) product middle.heap =
      .done nativeU middle.heap := by
    simpa only [nativeU, bodyEq, bodyRows] using outerDone
  have tag12 : compare (1 : Nat) 2 = .lt := by decide
  have bodyMuBranch : decision entered.1.key nativeB nativeU = .rightMu := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, nativeU, nativeB, bodyFresh, tag12]
  have bodyOrdinaryBranch : decision bodyEntered.1.key nativeB nativeB = .ordinary := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      Value.referenceOf, Value.free, nativeB, selectedBodyFresh]
  have nativeDone : execute top SourceEqualityPCSNativeEdge.conjoin 10 entered.1 nativeB nativeU initial =
      .done nativeU middle := by
    rw [execute]
    simp only [onNode, bodyMuBranch]
    change (execute top SourceEqualityPCSNativeEdge.conjoin 9 bodyEntered.1 nativeB nativeB bodyInitial).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity entry.identity) value after.heap) after) = _
    rw [execute]
    simp only [onNode, bodyOrdinaryBranch]
    change (node top SourceEqualityPCSNativeEdge.conjoin
      (execute top SourceEqualityPCSNativeEdge.conjoin 8 bodyEntered.1) bodyRows bodyRows bodyInitial).bind
      (fun value after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity entry.identity) value after.heap) after) = _
    rw [bodyDone, Result.bind, outerNode]
    rfl
  have done : execute top SourceEqualityPCSNativeEdge.conjoin 10 entered.1 body universeValue initial =
      .done universeValue middle := by
    simpa only [nativeB, nativeU, universeValue, bodyEq, bodyRows] using nativeDone
  refine ⟨10, middle, ?_, middleValid, totalGrowth⟩
  intro extra
  exact (execute_stable top SourceEqualityPCSNativeEdge.conjoin 10 extra entered.1
    body universeValue initial (by rw [done]; trivial)).trans done

end MicroCFTA.SourceSynthesisCurrentUniverseReferenceIdentity
