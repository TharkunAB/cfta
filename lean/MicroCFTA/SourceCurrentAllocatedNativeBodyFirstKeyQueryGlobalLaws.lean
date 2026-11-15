import MicroCFTA.SourceCurrentAllocatedNativeSourceQueryInduction
import MicroCFTA.SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeBodyFirstCoherentProductReplay
import MicroCFTA.SourceCurrentAllocatedNativeRawReferencePredicateReplay

/-!
# Body-first query history at the actual domain key

Each request retains its actual domain handle.
The selected key admits the original Mu, reference, and body requests.
The stronger row law uses targets at that same actual handle.
Both memo laws retain every original supplied-budget endpoint.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (pair repeatedValue)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The selected key retains all original pure, self, cutoff, and coherent body result clauses. -/
def NodeResult [DecidableEq Symbol] (sourceName bodyId : Nat)
    (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey)
    (body universeValue : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  SourceCurrentAllocatedNativePureQueryGlobalLaws.NodeResult request value ∧
    (request.domain.key = selectedKey → request.left = universeValue →
      request.right = .reference (.interned sourceName) →
      value = repeatedValue (pair bodyId sourceName)) ∧
    (request.domain.key = selectedKey → request.left = .reference (.interned sourceName) →
      request.right = .reference (.interned sourceName) →
      value = repeatedValue (pair bodyId sourceName)) ∧
    (request.domain.key = selectedKey → request.left = body → request.right = body →
      SourceCurrentAllocatedNativeCoherentOpenBodyResult.ProductShape sourceName bodyId sourceName body value)

/-- All rows retain the prior top law and selected-key targets at their actual domain handle. -/
def EdgeResult [DecidableEq Symbol] (sourceName bodyId : Nat)
    (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey) (universeValue : Value Symbol Guard)
    (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult request row ∧
    (request.domain.key = selectedKey →
      SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.EdgeResult
        ⟨request.domain, universeValue, .reference (.interned sourceName)⟩
        ⟨request.domain, .reference (.interned sourceName), .reference (.interned sourceName)⟩
        (repeatedValue (pair bodyId sourceName)) request row)

private theorem pure_known_result [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard) (value wanted : Value Symbol Guard)
    (actual : SourceCurrentAllocatedNativePureQueryGlobalLaws.NodeResult request value)
    (known : SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.KnownResult request wanted) :
    value = wanted := by
  rcases known with ⟨self, closed, same⟩ | selected
  · exact (actual.1 self closed).trans same.symm
  · exact actual.2 wanted selected

private theorem known_result_at_key [DecidableEq Symbol]
    (sourceName bodyId : Nat) (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey)
    (body universeValue : Value Symbol Guard) (request : NodeRequest Symbol Guard)
    (value wanted : Value Symbol Guard)
    (actual : NodeResult sourceName bodyId selectedKey body universeValue request value)
    (atKey : request.domain.key = selectedKey)
    (known : SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.KnownResult
      ⟨request.domain, universeValue, .reference (.interned sourceName)⟩
      ⟨request.domain, .reference (.interned sourceName), .reference (.interned sourceName)⟩
      (repeatedValue (pair bodyId sourceName)) request wanted) : value = wanted := by
  rcases known with previous | ⟨selected, same⟩
  · exact pure_known_result request value wanted actual.1 previous
  · rcases selected with mu | reference
    · exact (actual.2.1 atKey
        (congrArg (fun query : NodeRequest Symbol Guard => query.left) mu)
        (congrArg (fun query : NodeRequest Symbol Guard => query.right) mu)).trans same.symm
    · exact (actual.2.2.1 atKey
        (congrArg (fun query : NodeRequest Symbol Guard => query.left) reference)
        (congrArg (fun query : NodeRequest Symbol Guard => query.right) reference)).trans same.symm

private theorem ordered_values
    (R : (Value Symbol Guard × Value Symbol Guard) → Value Symbol Guard → Prop)
    {pairs : List (Value Symbol Guard × Value Symbol Guard)}
    {values expected : List (Value Symbol Guard)}
    (actual : All₂ (fun pair value => ∀ wanted, R pair wanted → value = wanted) pairs values)
    (selected : All₂ R pairs expected) : values = expected := by
  induction selected generalizing values with
  | nil => cases actual; rfl
  | cons chosen tail ih =>
      cases actual with
      | cons result rest => rw [result _ chosen, ih rest]

/-- Both query families retain same-key body-first laws at every original raw and budget endpoint. -/
theorem query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey) (bodyId : Nat)
    (compiled : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (nodeEdges body) (nodeEdges body))
    (selected : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      SourceRecursiveIntersectionControl.decision actualDomain.key
        (.mu entry body depth ordinary) (.reference (.interned entry.identity)) = .leftMu)
    (childPure : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current actualDomain.key
        (.mu entry body depth ordinary) (.reference (.interned entry.identity))
        entry.identity entry.identity).1,
        SourceRecursiveIntersectionKernel.body (.mu entry body depth ordinary),
        SourceRecursiveIntersectionKernel.body (.reference (.interned entry.identity))⟩ =
        .pure (repeatedValue (pair bodyId entry.identity)))
    (absent : let binder := pair entry.identity entry.identity
      Reference.intersection binder.1 binder.2 ∉
      (repeatedValue (pair bodyId entry.identity) : Value Symbol Guard).free)
    (read : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey → ∀ current : Checked width, Physical current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨actualDomain, .reference (.interned entry.identity),
          .reference (.interned entry.identity)⟩)) current =
        .yielded (.code (requestNode actualDomain (.mu entry body depth ordinary)
          (.reference (.interned entry.identity)))) current)
    (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.node request .pure)) before →
      FieldsThrough fuel (.code (.node request .pure)) before →
      Returned (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)) before.native.nodes →
      Returned (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)) before.native.edges →
      (Returned (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)) (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
        Returned (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)) (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
        (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)) request value)) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.edge request .pure)) before →
      FieldsThrough fuel (.code (.edge request .pure)) before →
      Returned (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)) before.native.nodes →
      Returned (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)) before.native.edges →
      (Returned (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)) (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
        Returned (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)) (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
        (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)) request value)) := by
  refine SourceCurrentAllocatedNativeSourceQueryInduction.query_returned_and_raw_results
    (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary))
    (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)) sourceHeap ?_ ?_ fuel
  · intro request before bodyState middle parentFuel bodySteps value next
      physical growth valid plan fields entered firstGrowth _firstValid smaller actual nodeCalls edgeCalls
    constructor
    · constructor
      · apply SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
          request before bodyState middle parentFuel bodySteps value next entered smaller actual
        intro childSteps _small childNext childValue childAfter childEntry childTrace closed
        exact (nodeCalls ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.left⟩
          childNext bodyState childAfter 1 childSteps childValue (by decide) (by omega)
          childEntry childTrace).1.1 rfl closed
      · exact SourceCurrentAllocatedNativePureQueryLaw.raw_result
          request bodyState middle bodySteps value actual
    · constructor
      · intro atKey leftSame rightSame
        rcases request with ⟨domain, left, right⟩
        change left = .mu entry body depth ordinary at leftSame
        change right = .reference (.interned entry.identity) at rightSame
        subst left
        subst right
        change domain.key = selectedKey at atKey
        have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
          parentFuel 1 (.code (.node ⟨domain, .mu entry body depth ordinary,
            .reference (.interned entry.identity)⟩ .pure))
          (.code (compileNode ⟨domain, .mu entry body depth ordinary,
            .reference (.interned entry.identity)⟩)) next
          before bodyState physical plan entered (by omega)
        let allocated := SourceRecursiveIntersectionEnvironment.enter bodyState.native.machine.domains
          domain.key (.mu entry body depth ordinary) (.reference (.interned entry.identity))
          entry.identity entry.identity
        let started : Checked width :=
          {bodyState with native := advance bodyState.native {bodyState.native.machine with domains := allocated.2}}
        have canonical : compileNode ⟨allocated.1,
            SourceRecursiveIntersectionKernel.body (.mu entry body depth ordinary),
            SourceRecursiveIntersectionKernel.body (.reference (.interned entry.identity))⟩ =
            .pure (repeatedValue (pair bodyId entry.identity)) :=
          childPure domain atKey bodyState.native.machine.domains reached.2.1.machine.2
        have observed := SourceCurrentAllocatedNativeRawMuCutoffReplay.left_mu_cutoff_trace_result
          ⟨domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
          before bodyState middle parentFuel bodySteps value (repeatedValue (pair bodyId entry.identity))
          entry.identity entry.identity next (selected domain atKey) rfl rfl canonical absent
          entered smaller actual (by
            dsimp only
            intro used count positive bounded _small childNext childValue childAfter childEntry childTrace pure
            exact (nodeCalls ⟨allocated.1,
                SourceRecursiveIntersectionKernel.body (.mu entry body depth ordinary),
                SourceRecursiveIntersectionKernel.body (.reference (.interned entry.identity))⟩
              childNext started childAfter used count childValue positive bounded childEntry childTrace).1.2
                (repeatedValue (pair bodyId entry.identity)) pure)
        exact observed.1
      · constructor
        · intro atKey leftSame rightSame
          rcases request with ⟨domain, left, right⟩
          change left = .reference (.interned entry.identity) at leftSame
          change right = .reference (.interned entry.identity) at rightSame
          subst left
          subst right
          change domain.key = selectedKey at atKey
          have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
            parentFuel 1 (.code (.node ⟨domain, .reference (.interned entry.identity),
              .reference (.interned entry.identity)⟩ .pure))
            (.code (compileNode ⟨domain, .reference (.interned entry.identity),
              .reference (.interned entry.identity)⟩)) next
            before bodyState physical plan entered (by omega)
          have actualRead := read domain atKey bodyState reached.2.1 firstGrowth
          have observed := SourceCurrentAllocatedNativeRawReferencePredicateReplay.reference_trace_predicate_of_actual_read
            ⟨domain, .reference (.interned entry.identity), .reference (.interned entry.identity)⟩
            ⟨domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
            before bodyState middle parentFuel bodySteps value
            (fun child => child = repeatedValue (pair bodyId entry.identity)) next
            actualRead entered smaller actual (by
              intro used count positive bounded _small childNext childValue childAfter childEntry childTrace
              exact (nodeCalls ⟨domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
                childNext bodyState childAfter used count childValue positive bounded childEntry childTrace).2.1 atKey rfl rfl)
          exact observed.1
        · intro atKey leftSame rightSame
          rcases request with ⟨domain, left, right⟩
          change left = body at leftSame
          change right = body at rightSame
          subst left
          subst right
          change domain.key = selectedKey at atKey
          have observed := SourceCurrentAllocatedNativeBodyFirstCoherentProductReplay.open_body_product_of_reference_row_traces
            lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
            bodyId entry.identity domain before bodyState middle parentFuel bodySteps value next
            (compiled domain atKey) physical growth valid plan fields entered smaller actual (by
              intro pair member childNext childBefore childAfter used count childValue
                positive bounded origin childTrace
              have property := edgeCalls ⟨domain, pair.1, pair.2⟩ childNext childBefore childAfter
                used count childValue positive bounded origin childTrace
              exact property.2 atKey)
          exact observed.1
  · intro request before first middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered _firstGrowth firstValid smaller actual nodeCalls _edgeCalls
    have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
      parentFuel 1 (.code (.edge request .pure)) (.edgeBody request .pure) next
      before first physical plan entered (by omega)
    have mismatch : SourceCurrentAllocatedNativeQueryGlobalLaws.MismatchResult request value := by
      intro different
      exact (SourceCurrentAllocatedNativeRawBodyResults.mismatch_edge_body_trace_result
        request first middle bodySteps value reached.2.1 different actual).1
    have oldTop : SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.TopRowResult request value := by
      intro self sourceTop wanted selectedChildren
      have readback := SourceCurrentAllocatedNativeTopRowBodyReadback.self_top_body_readback_of_smaller_nodes
        (fun pair result => ∀ selectedValue,
          SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.KnownResult
            ⟨request.domain, pair.1, pair.2⟩ selectedValue → result = selectedValue)
        request before first middle parentFuel bodySteps value next self sourceTop
        reached.2.1 firstValid entered smaller reached.2.2.2.2 actual (by
          intro used count positive bounded _small pair _member childNext childBefore childAfter childValue
            origin _childPhysical childTrace selectedValue known
          have property := nodeCalls ⟨request.domain, pair.1, pair.2⟩ childNext childBefore childAfter
            used count childValue positive bounded origin childTrace
          exact pure_known_result ⟨request.domain, pair.1, pair.2⟩ childValue selectedValue property.1 known)
      have same := ordered_values
        (fun pair result => SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.KnownResult
          ⟨request.domain, pair.1, pair.2⟩ result) readback.1 selectedChildren
      exact ⟨same, by simpa only [same] using readback.2.1⟩
    refine ⟨⟨mismatch, oldTop⟩, ?_⟩
    intro atKey
    refine ⟨mismatch, ?_⟩
    intro self sourceTop wanted selectedChildren
    have readback := SourceCurrentAllocatedNativeTopRowBodyReadback.self_top_body_readback_of_smaller_nodes
      (fun pair result => ∀ selectedValue,
        SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.KnownResult
          ⟨request.domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
          ⟨request.domain, .reference (.interned entry.identity), .reference (.interned entry.identity)⟩
          (repeatedValue (SourceRecursiveIntersectionControl.pair bodyId entry.identity))
            ⟨request.domain, pair.1, pair.2⟩ selectedValue →
            result = selectedValue)
      request before first middle parentFuel bodySteps value next self sourceTop
      reached.2.1 firstValid entered smaller reached.2.2.2.2 actual (by
        intro used count positive bounded _small pair _member childNext childBefore childAfter childValue
          origin _childPhysical childTrace selectedValue known
        have property := nodeCalls ⟨request.domain, pair.1, pair.2⟩ childNext childBefore childAfter
          used count childValue positive bounded origin childTrace
        exact known_result_at_key entry.identity bodyId selectedKey body (.mu entry body depth ordinary)
          ⟨request.domain, pair.1, pair.2⟩ childValue selectedValue property atKey known)
    have same := ordered_values
      (fun pair result => SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.KnownResult
        ⟨request.domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
        ⟨request.domain, .reference (.interned entry.identity), .reference (.interned entry.identity)⟩
        (repeatedValue (SourceRecursiveIntersectionControl.pair bodyId entry.identity))
        ⟨request.domain, pair.1, pair.2⟩ result) readback.1 selectedChildren
    exact ⟨same, by simpa only [same] using readback.2.1⟩

/-- Both actual initial memo tables supply every same-key body-first clause. -/
theorem initial_node_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey) (bodyId : Nat)
    (compiled : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (nodeEdges body) (nodeEdges body))
    (selected : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      SourceRecursiveIntersectionControl.decision actualDomain.key
        (.mu entry body depth ordinary) (.reference (.interned entry.identity)) = .leftMu)
    (childPure : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current actualDomain.key
        (.mu entry body depth ordinary) (.reference (.interned entry.identity))
        entry.identity entry.identity).1,
        SourceRecursiveIntersectionKernel.body (.mu entry body depth ordinary),
        SourceRecursiveIntersectionKernel.body (.reference (.interned entry.identity))⟩ =
        .pure (repeatedValue (pair bodyId entry.identity)))
    (absent : let binder := pair entry.identity entry.identity
      Reference.intersection binder.1 binder.2 ∉
      (repeatedValue (pair bodyId entry.identity) : Value Symbol Guard).free)
    (read : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey → ∀ current : Checked width, Physical current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨actualDomain, .reference (.interned entry.identity),
          .reference (.interned entry.identity)⟩)) current =
        .yielded (.code (requestNode actualDomain (.mu entry body depth ordinary)
          (.reference (.interned entry.identity)))) current)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : NodeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩) :
    (Returned (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)) (execute fuel (.code (.node request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)) (execute fuel (.code (.node request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.node request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)) request value) := by
  exact (query_returned_and_raw_results lib query signed whole accepted rootValue sourceHeap built
    key entry body depth ordinary stored selectedKey bodyId compiled selected childPure absent read fuel).1
    request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    sourceGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty
      (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)))
    (SourceCurrentAllocatedNativeContextCache.returned_empty
      (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)))

/-- Both actual initial memo tables supply every same-key body-first clause. -/
theorem initial_edge_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (selectedKey : IntersectionFlatMemoKeyDomain.DomainKey) (bodyId : Nat)
    (compiled : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (nodeEdges body) (nodeEdges body))
    (selected : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      SourceRecursiveIntersectionControl.decision actualDomain.key
        (.mu entry body depth ordinary) (.reference (.interned entry.identity)) = .leftMu)
    (childPure : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current actualDomain.key
        (.mu entry body depth ordinary) (.reference (.interned entry.identity))
        entry.identity entry.identity).1,
        SourceRecursiveIntersectionKernel.body (.mu entry body depth ordinary),
        SourceRecursiveIntersectionKernel.body (.reference (.interned entry.identity))⟩ =
        .pure (repeatedValue (pair bodyId entry.identity)))
    (absent : let binder := pair entry.identity entry.identity
      Reference.intersection binder.1 binder.2 ∉
      (repeatedValue (pair bodyId entry.identity) : Value Symbol Guard).free)
    (read : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey → ∀ current : Checked width, Physical current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨actualDomain, .reference (.interned entry.identity),
          .reference (.interned entry.identity)⟩)) current =
        .yielded (.code (requestNode actualDomain (.mu entry body depth ordinary)
          (.reference (.interned entry.identity)))) current)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat) (request : EdgeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩)
    (fields : FieldsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩) :
    (Returned (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)) (execute fuel (.code (.edge request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)) (execute fuel (.code (.edge request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.edge request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)) request value) := by
  exact (query_returned_and_raw_results lib query signed whole accepted rootValue sourceHeap built
    key entry body depth ordinary stored selectedKey bodyId compiled selected childPure absent read fuel).2
    request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    sourceGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty
      (NodeResult entry.identity bodyId selectedKey body (.mu entry body depth ordinary)))
    (SourceCurrentAllocatedNativeContextCache.returned_empty
      (EdgeResult entry.identity bodyId selectedKey (.mu entry body depth ordinary)))

end MicroCFTA.SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws
