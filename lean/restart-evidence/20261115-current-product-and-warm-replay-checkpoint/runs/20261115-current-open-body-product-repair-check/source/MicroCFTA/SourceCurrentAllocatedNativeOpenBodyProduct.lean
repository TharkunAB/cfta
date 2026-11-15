import MicroCFTA.SourceCurrentAllocatedNativeDiagonalProductReadback
import MicroCFTA.SourceCurrentAllocatedNativeOpenBodyMetadata
import MicroCFTA.SourceSynthesisCurrentUniverseBodyMatchedPairs
import MicroCFTA.SourceCurrentAllocatedNativeOpenProductReclosure

/-!
# Actual current-source body products and reclosure

The same completed row scan supplies the concrete transformed products.
Current source shape classifies every actual pair and proves row liveness.
The constructor returns the open product with its exact cutoff metadata.
Optional construction returns original U at the same full returned state.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeOpenBodyProduct
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open IntersectionFlatMemoKeyDomain (DomainKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (repeatedValue)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable {width : Nat}

set_option autoImplicit false

/-- The actual current-source row scan derives its open product and same-state reclosure from smaller query laws. -/
theorem current_open_body_product_of_smaller_queries
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (cutoffLeft cutoffRight : Nat) (domain : Interned DomainKey)
    (before after : Checked width) (fuel traceFuel : Nat) (result : Value Symbol Guard)
    (physical : Physical before.native) (growth : Grows sourceHeap before.native.machine.heap)
    (done : SourceEqualityNativeDemand.execute fuel
      (.code (compileRows domain (nodeEdges body) (nodeEdges body))) before = .done result after)
    (actual : Trace traceFuel (.code (compileRows domain (nodeEdges body) (nodeEdges body))) before
      (.code (.pure result)) after)
    (children : ∀ stepsBefore childFuel, stepsBefore + childFuel < fuel → childFuel < fuel →
      ∀ pair ∈ pairs (nodeEdges body) (nodeEdges body),
      ∀ (next : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (first last : Checked width) (row : EdgeValue Symbol Guard),
      Steps stepsBefore (.code (compileRows domain (nodeEdges body) (nodeEdges body))) before
        (.code ((requestEdge domain pair.1 pair.2).bind next)) first →
      Physical first.native →
      SourceEqualityNativeDemand.execute childFuel (.code (requestEdge domain pair.1 pair.2)) first = .done row last →
      (pair.1 = pair.2 →
        row.children = pair.1.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
        row.entry.key = ⟨pair.1.entry.key.symbol,
          (pair.1.children.map (input (replacement (.interned entry.identity)
            (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).map Value.referenceOf,
          top⟩) ∧
      (pair.1.children.length ≠ pair.2.children.length → row.children = [.empty])) :
    ∃ (productEntry : Interned NodeKey) (products rawRows : List (EdgeValue Symbol Guard))
      (middle : Checked width) (count : Nat),
      count + 1 < fuel ∧
      All₂ (fun (source : EdgeValue Symbol Guard) target =>
        target.children = source.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)))) ∧
        target.entry.key = ⟨source.entry.key.symbol,
          (source.children.map (input (replacement (.interned entry.identity)
            (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))).map Value.referenceOf,
          top⟩) (nodeEdges body) products ∧
      (∀ row ∈ products, row ∈ rawRows) ∧
      Physical middle.native ∧ Extension before.native.machine middle.native.machine ∧
      (∀ row ∈ products, EdgeResident middle.native.machine.heap row) ∧
      Trace count (.code (compileRows domain (nodeEdges body) (nodeEdges body))) before
        (.code (.work (makeNode rawRows) .pure)) middle ∧
      result = (run (makeNode rawRows) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeNode rawRows) middle.native.machine.heap).2}} ∧
      canonicalEdges (surviving rawRows) = canonicalEdges products ∧
      result = .node productEntry (canonicalEdges products) 0
        [.intersection (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight).1
          (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight).2] ∧
      Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      Available after.native.machine.heap result ∧
      (∀ row ∈ products, EdgeResident after.native.machine.heap row) ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight)
        result after.native.machine.heap = .done (.mu entry body depth ordinary) after.native.machine.heap ∧
      SourceEqualityNativeDemand.step
        (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight) result .pure)) after =
        .yielded (.code (.pure (.mu entry body depth ordinary))) after ∧
      SourceEqualityNativeDemand.execute 2
        (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight) result .pure)) after =
        .done (.mu entry body depth ordinary) after := by
  let cutoff := SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight
  let rewrite : Value Symbol Guard → Value Symbol Guard :=
    input (replacement (.interned entry.identity) (repeatedValue cutoff))
  obtain ⟨_bodyEntry, marker, arrow, rows, bodyEq, _bodyAvailable, markerRead, _arrowChildren,
      _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms, kinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      before.native.machine.heap physical.machine.1 growth
  obtain ⟨_markerEntry, _markerRow, markerEq, _markerLeaf, _markerKey⟩ := markerRead
  have sourceRows : nodeEdges body = canonicalEdges (arrow :: rows) := by
    rw [bodyEq]
    rfl
  have markerInput : rewrite marker = marker := by
    rw [markerEq]
    rfl
  have referenceInput : rewrite (.reference (.interned entry.identity) : Value Symbol Guard) = repeatedValue cutoff := by
    simp [rewrite, input, replacement]
  have live : ∀ source ∈ nodeEdges body,
      (source.children.map rewrite).any (fun child => child.referenceOf == .empty) = false := by
    intro source member
    have included : source ∈ canonicalEdges (arrow :: rows) := by
      rw [← sourceRows]
      exact member
    apply List.any_eq_false.mpr
    intro child present
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp present
    rcases (kinds source included).2.2 original originalMember with same | same
    · rw [same, referenceInput]
      simp [repeatedValue, Value.referenceOf]
    · rw [same.1, markerInput, markerEq]
      simp [Value.referenceOf]
  obtain ⟨_pairEntry, pairRows, pairBody, classified⟩ :=
    SourceSynthesisCurrentUniverseBodyMatchedPairs.current_stored_universe_body_matching_pairs
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      before.native.machine.heap physical.machine.1 growth
  have pairRowsEq : nodeEdges body = pairRows := by
    rw [pairBody]
    rfl
  have classify : ∀ pair ∈ pairs (nodeEdges body) (nodeEdges body),
      pair.1 = pair.2 ∨ pair.1.children.length ≠ pair.2.children.length := by
    simpa only [pairRowsEq] using classified
  have observed := SourceCurrentAllocatedNativeDiagonalProductReadback.diagonal_product_of_smaller_queries
    entry.identity cutoffLeft cutoffRight domain (nodeEdges body) before after fuel traceFuel result
    live physical done actual (by
      intro stepsBefore childFuel room smaller pair member next first last row origin firstPhysical childDone
      have law := children stepsBefore childFuel room smaller pair member next first last row
        origin firstPhysical childDone
      refine ⟨law.1, ?_⟩
      intro distinct
      rcases classify pair member with same | mismatch
      · exact False.elim (distinct same)
      · exact law.2 mismatch)
  obtain ⟨products, rawRows, middle, count, bounded, aligned, retained, middleResident, throughWork,
      resultEq, afterEq, canonical, _edgesEq, _freeEq, middlePhysical, middleExtension,
      afterPhysical, afterExtension, available, afterResident⟩ := observed
  have middleGrowth := grows_trans growth middleExtension.heap
  have metadata := SourceCurrentAllocatedNativeOpenBodyMetadata.current_transformed_body_metadata_after_growth
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    middle.native.machine.heap middlePhysical.machine.1 middleGrowth cutoff products (by cases bodyEq; exact aligned) middleResident
  have nonempty : canonicalEdges products ≠ [] := by
    intro absent
    have impossible := metadata.2
    rw [absent] at impossible
    simp [childFree, canonicalFree] at impossible
  have productRead : ∃ productEntry : Interned NodeKey,
      result = .node productEntry (canonicalEdges products) 0 [.intersection cutoff.1 cutoff.2] := by
    cases kept : canonicalEdges products with
    | nil => exact (nonempty (by simp only [kept])).elim
    | cons first rest =>
        have selected : ∀ row ∈ first :: rest, EdgeResident middle.native.machine.heap row := by
          intro row member
          apply middleResident row
          apply canonicalEdges_member products row
          rw [kept]
          exact member
        obtain ⟨productEntry, nodeFields⟩ := identifyNode_readback (first :: rest)
          middle.native.machine.heap middlePhysical.machine.1.coherent middlePhysical.machine.1.linked selected
        have shape : result = .node productEntry (canonicalEdges products)
            (maximumDepth ((canonicalEdges products).flatMap EdgeValue.children))
            (childFree ((canonicalEdges products).flatMap EdgeValue.children)) := by
          rw [resultEq]
          simpa only [makeNode, canonical, kept, run, identifyNode] using nodeFields
        rw [metadata.1, metadata.2] at shape
        exact ⟨productEntry, by simpa only [kept] using shape⟩
  obtain ⟨productEntry, nodeRead⟩ := productRead
  have afterGrowth := grows_trans growth afterExtension.heap
  have reclosed := SourceCurrentAllocatedNativeOpenProductReclosure.stored_open_product_optional_reclosure
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    after afterPhysical.machine.1 afterGrowth cutoff result productEntry products nodeRead available (by cases bodyEq; exact aligned) afterResident
  exact ⟨productEntry, products, rawRows, middle, count, bounded, aligned, retained,
    middlePhysical, middleExtension, middleResident, throughWork, resultEq, afterEq, canonical,
    nodeRead, afterPhysical, afterExtension, available, afterResident, reclosed⟩

end MicroCFTA.SourceCurrentAllocatedNativeOpenBodyProduct

set_option warningAsError true
#check MicroCFTA.SourceCurrentAllocatedNativeOpenBodyProduct.current_open_body_product_of_smaller_queries
#print axioms MicroCFTA.SourceCurrentAllocatedNativeOpenBodyProduct.current_open_body_product_of_smaller_queries
