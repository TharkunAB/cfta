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
  let initial : Machine Symbol Guard := ⟨heap, domains⟩
  have checked := InternedFreshOrdinaryFacts.build_verified (ordinarySymbols whole) [] empty
    InternedNestedFacts.empty_facts (by intro value member; cases member)
  have facts : Facts heap := by
    simpa only [built, Outcome.state] using checked.facts
  have rootAvailable : Available heap rootValue := checked.result rootValue heap built
  have universeAvailable : Available heap (.mu entry body depth ordinary) := facts.cached.nodes key _ stored
  have referenceAvailable : Available heap (.reference (.interned entry.identity)) :=
    reference_available_mu heap facts entry body depth ordinary universeAvailable
  have bodyReplay := SourceSynthesisCurrentUniverseOwnership.current_stored_universe_body_replay
    lib query signed whole accepted rootValue heap built key entry body depth ordinary stored heap (grows_refl heap)
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
      lib query signed whole accepted rootValue heap built key entry body depth ordinary stored
  have probeMarkerSame : Value.node probeMarkerEntry [probeMarkerRow] 0 [] = .node m [markerRow] 0 [] :=
    SourceSynthesisUniverseMappedProbeRows.marker_eq (literal "(->)") top
      probeMarkerEntry m probeMarkerRow markerRow heap facts probeMarkerAvailable nativeMarker probeMarkerKey markerKey
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
        probeAligned, probeAvailable, probeResident, _probeKinds, _probeRetained⟩ := probePackets ordinaryProbe
    have nativeProbeChildren : probeArrow.children = [.node m [markerRow] 0 [], .reference probe, .reference probe] := by
      simpa only [probeMarkerSame] using probeChildren
    have nativeProbeKey : probeArrow.entry.key = ⟨literal "->", [(Value.node m [markerRow] 0 []).referenceOf,
        .ref probe, .ref probe], top⟩ := by
      simpa only [probeMarkerSame] using probeKey
    have probeCurrent : ∀ row ∈ probeArrow :: probeRows, EdgeResident middle.heap row := by
      intro row member
      exact edge_grows heap middle.heap totalGrowth.heap row (probeResident row member)
    have targetCurrent : Available middle.heap target := totalGrowth.available _ probeAvailable
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
  have incomingCovered := InternedFreshOrdinaryCoverage.closed_covered (ordinarySymbols whole) rootValue heap built
  have finalCovered : InternedRecordCoherence.Covered [] middle.heap :=
    SourceRecursiveIntersectionKernelCoverage.execute_covered (pending := []) top SourceEqualityPCSNativeEdge.conjoin
      13 IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity)) (.mu entry body depth ordinary)
      initial initialValid (empty_domain initial) referenceAvailable universeAvailable incomingCovered
      (.mu entry body depth ordinary) middle done
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed (ordinarySymbols whole) rootValue heap built
  have scopeResult := SourceRecursiveIntersectionScopeCalls.execute_scoped top SourceEqualityPCSNativeEdge.conjoin
    13 IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity)) (.mu entry body depth ordinary)
    initial initialValid (empty_domain initial) referenceAvailable universeAvailable semantic
    (.mu entry body depth ordinary) middle done
  refine ⟨middle, done, middleValid, scopeResult.1, totalGrowth, finalCovered, finalUniverse,
    totalGrowth.available _ rootAvailable, totalGrowth.heap.nodeRecords key _ stored, ?_⟩
  intro extra
  exact (SourceRecursiveIntersectionKernel.execute_stable top SourceEqualityPCSNativeEdge.conjoin
    13 extra IntersectionEmptyDomain.emptyDomain (.reference (.interned entry.identity))
    (.mu entry body depth ordinary) initial (by rw [done]; trivial)).trans done


end MicroCFTA.SourceSynthesisCurrentUniverseReferenceIdentity
