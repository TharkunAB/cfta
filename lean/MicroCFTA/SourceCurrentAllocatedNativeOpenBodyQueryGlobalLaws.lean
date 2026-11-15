import MicroCFTA.SourceCurrentAllocatedNativeSourceQueryInduction
import MicroCFTA.SourceCurrentAllocatedNativeTopRowQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeRawOpenBodyProductReplay

/-!
# Open original-body results from actual native query history

The node law retains the existing closed-self and literal pure clauses.
A same-key original-body query also returns its exact open row product.
The existing top-row law retains every ordered child and full source key.
Both memo laws hold at every original supplied-budget endpoint.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeOpenBodyQueryGlobalLaws
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (KnownResult EdgeResult)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (repeatedValue pair)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

def ProductShape (sourceName cutoffLeft cutoffRight : Nat) (body value : Value Symbol Guard) : Prop :=
  ∃ (productEntry : Interned NodeKey) (products : List (EdgeValue Symbol Guard)),
    All₂ (fun (source : EdgeValue Symbol Guard) target =>
      target.children = source.children.map (input (replacement (.interned sourceName)
        (repeatedValue (pair cutoffLeft cutoffRight)))) ∧
      target.entry.key = ⟨source.entry.key.symbol,
        (source.children.map (input (replacement (.interned sourceName)
          (repeatedValue (pair cutoffLeft cutoffRight))))).map Value.referenceOf, top⟩)
      (nodeEdges body) products ∧
    value = .node productEntry (canonicalEdges products) 0
      [.intersection (pair cutoffLeft cutoffRight).1 (pair cutoffLeft cutoffRight).2]

def NodeResult [DecidableEq Symbol] (sourceName cutoffLeft cutoffRight : Nat)
    (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey) (body : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  SourceCurrentAllocatedNativePureQueryGlobalLaws.NodeResult request value ∧
    (request.domain.key = selectedKey → request.left = body → request.right = body →
      ProductShape sourceName cutoffLeft cutoffRight body value)

private theorem known_result [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard) (value expected : Value Symbol Guard)
    (actual : SourceCurrentAllocatedNativePureQueryGlobalLaws.NodeResult request value) (known : KnownResult request expected) :
    value = expected := by
  rcases known with ⟨self, closed, same⟩ | selected
  · exact (actual.1 self closed).trans same.symm
  · exact actual.2 expected selected

private theorem ordered_values [DecidableEq Symbol]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    {pairs : List (Value Symbol Guard × Value Symbol Guard)}
    {values expected : List (Value Symbol Guard)}
    (actual : Language.All₂ (fun pair value => ∀ wanted,
      KnownResult ⟨domain, pair.1, pair.2⟩ wanted → value = wanted) pairs values)
    (selected : Language.All₂ (fun pair value => KnownResult ⟨domain, pair.1, pair.2⟩ value)
      pairs expected) : values = expected := by
  induction selected generalizing values with
  | nil => cases actual; rfl
  | cons chosen tail ih =>
      cases actual with
      | cons result rest => rw [result _ chosen, ih rest]

set_option maxHeartbeats 1600000 in
/-- Both query families retain the open body clause and all existing laws at every original endpoint. -/
theorem query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey) (cutoffLeft cutoffRight : Nat)
    (compiled : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (nodeEdges body) (nodeEdges body))
    (inputs : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey → ∀ row ∈ nodeEdges body,
      All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
        KnownResult ⟨actualDomain, children.1, children.2⟩ value)
        (row.children.zip row.children)
        (row.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (pair cutoffLeft cutoffRight))))))
    (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.node request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.node request .pure)) before →
      Returned (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body) before.native.nodes → Returned EdgeResult before.native.edges →
      (Returned (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body) (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
        Returned EdgeResult (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
        (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body) request value)) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.edge request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.edge request .pure)) before →
      Returned (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body) before.native.nodes → Returned EdgeResult before.native.edges →
      (Returned (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body) (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
        Returned EdgeResult (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
        EdgeResult request value)) := by
  refine SourceCurrentAllocatedNativeSourceQueryInduction.query_returned_and_raw_results
    (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body) EdgeResult sourceHeap ?_ ?_ fuel
  · intro request before first middle parentFuel bodySteps value next
      physical growth valid plan fields entered _firstGrowth _firstValid smaller actual nodeCalls edgeCalls
    constructor
    · constructor
      · apply SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
          request before first middle parentFuel bodySteps value next entered smaller actual
        intro childSteps _small childNext childValue childAfter childEntry childTrace closed
        exact (nodeCalls ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.left⟩
          childNext first childAfter 1 childSteps childValue (by decide) (by omega)
          childEntry childTrace).1.1 rfl closed
      · exact SourceCurrentAllocatedNativePureQueryLaw.raw_result
          request first middle bodySteps value actual
    · intro keySame leftSame rightSame
      rcases request with ⟨domain, left, right⟩
      change left = body at leftSame
      change right = body at rightSame
      subst left
      subst right
      change domain.key = selectedKey at keySame
      obtain ⟨_bodyEntry, _marker, arrow, rows, bodyShape, _bodyAvailable, _markerShape,
          _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
          childKinds, _arrowPresent⟩ :=
        SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          before.native.machine.heap physical.machine.1 growth
      have sourceRows : nodeEdges body = canonicalEdges (arrow :: rows) := by
        rw [bodyShape]
        rfl
      have sourceTop (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges body) :
          row.entry.key.constraint = top :=
        (childKinds row (by rw [← sourceRows]; exact member)).2.1
      have observed := SourceCurrentAllocatedNativeRawOpenBodyProductReplay.open_body_product_trace_result
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        cutoffLeft cutoffRight domain before first middle parentFuel bodySteps value next
        (compiled domain keySame) physical growth valid plan fields entered smaller actual (by
          intro pair member childNext childBefore childAfter used count childValue
            positive bounded origin childTrace
          have property := edgeCalls ⟨domain, pair.1, pair.2⟩ childNext childBefore childAfter
            used count childValue positive bounded origin childTrace
          refine ⟨?_, property.1⟩
          intro self
          have sourceMember := (SourceRecursiveIntersectionKernel.pairs_member
            (nodeEdges body) (nodeEdges body) pair).mp member
          have selectedInputs :
              All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (wanted : Value Symbol Guard) =>
                KnownResult ⟨domain, children.1, children.2⟩ wanted)
                (pair.1.children.zip pair.2.children)
                (pair.1.children.map (input (replacement (.interned entry.identity)
                  (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))))) := by
            rw [← self]
            exact inputs domain keySame pair.1 sourceMember.1
          exact property.2 self.symm (sourceTop pair.1 sourceMember.1) _ selectedInputs)
      obtain ⟨productEntry, products, _rawRows, _workMiddle, _count, _bounded, aligned, _retained,
          _middlePhysical, _middleExtension, _middleResident, _throughWork, _resultEq, _afterEq,
          _canonical, nodeRead, _afterPhysical, _afterExtension, _originalExtension, _afterGrowth,
          _available, _afterResident, _reclosed, _optionalStep, _optionalDone⟩ := observed
      exact ⟨productEntry, products, aligned, nodeRead⟩
  · intro request before first middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered _firstGrowth firstValid smaller actual nodeCalls _edgeCalls
    have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
      parentFuel 1 (.code (.edge request .pure)) (.edgeBody request .pure) next
      before first physical plan entered (by omega)
    constructor
    · intro mismatch
      exact (SourceCurrentAllocatedNativeRawBodyResults.mismatch_edge_body_trace_result
        request first middle bodySteps value reached.2.1 mismatch actual).1
    · intro self sourceTop expected selected
      have readback := SourceCurrentAllocatedNativeTopRowBodyReadback.self_top_body_readback_of_smaller_nodes
        (fun pair result => ∀ wanted, KnownResult ⟨request.domain, pair.1, pair.2⟩ wanted → result = wanted)
        request before first middle parentFuel bodySteps value next self sourceTop
        reached.2.1 firstValid entered smaller reached.2.2.2.2 actual (by
          intro used count positive bounded _small pair _member childNext childBefore childAfter childValue
            origin _childPhysical childTrace wanted known
          have property := nodeCalls ⟨request.domain, pair.1, pair.2⟩ childNext childBefore childAfter
            used count childValue positive bounded origin childTrace
          exact known_result ⟨request.domain, pair.1, pair.2⟩ childValue wanted property.1 known)
      have same := ordered_values request.domain readback.1 selected
      exact ⟨same, by simpa only [same] using readback.2.1⟩

/-- Actual whole-memo initialization supplies the node and edge laws for the original node query. -/
theorem initial_node_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey) (cutoffLeft cutoffRight : Nat)
    (compiled : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (nodeEdges body) (nodeEdges body))
    (inputs : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey → ∀ row ∈ nodeEdges body,
      All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
        KnownResult ⟨actualDomain, children.1, children.2⟩ value)
        (row.children.zip row.children)
        (row.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (pair cutoffLeft cutoffRight))))))
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : NodeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩) :
    (Returned (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body) (execute fuel (.code (.node request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned EdgeResult (execute fuel (.code (.node request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.node request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body) request value) := by
  exact (query_returned_and_raw_results (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    selectedKey cutoffLeft cutoffRight compiled inputs fuel).1 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    sourceGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty
      (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body))
    (SourceCurrentAllocatedNativeContextCache.returned_empty EdgeResult)

/-- Actual whole-memo initialization supplies the node and edge laws for the original edge query. -/
theorem initial_edge_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey) (cutoffLeft cutoffRight : Nat)
    (compiled : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (nodeEdges body) (nodeEdges body))
    (inputs : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey → ∀ row ∈ nodeEdges body,
      All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
        KnownResult ⟨actualDomain, children.1, children.2⟩ value)
        (row.children.zip row.children)
        (row.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (pair cutoffLeft cutoffRight))))))
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : EdgeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩) :
    (Returned (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body) (execute fuel (.code (.edge request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned EdgeResult (execute fuel (.code (.edge request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.edge request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      EdgeResult request value) := by
  exact (query_returned_and_raw_results (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    selectedKey cutoffLeft cutoffRight compiled inputs fuel).2 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    sourceGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty
      (NodeResult entry.identity cutoffLeft cutoffRight selectedKey body))
    (SourceCurrentAllocatedNativeContextCache.returned_empty EdgeResult)

end MicroCFTA.SourceCurrentAllocatedNativeOpenBodyQueryGlobalLaws
