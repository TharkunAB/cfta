import MicroCFTA.SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstOuterReclosure
import MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff
import MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstReferenceRead

/-!
# The actual body-first outer source Mu result through warm history

The complete current body-first node and edge laws remain exact.
The original full pattern fixes the added original-domain B/U clause.
Actual smaller B/B queries supply coherent products at the entered key.
The used outer binder recloses full U at that same child endpoint.
Both complete empty initializations retain the original plans and fuel.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeBodyFirstOuterQueryGlobalLaws
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
open SourceRecursiveIntersectionControl (identity tag decision pair repeatedValue)
open SourceRecursiveIntersectionDomain
open SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws (EdgeResult)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

def NodeResult [DecidableEq Symbol] (sourceName bodyId : Nat)
    (selectedKey originalKey : IntersectionFlatMemoKeyDomain.DomainKey)
    (body universeValue : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
    sourceName bodyId selectedKey body universeValue request value ∧
  (request.domain.key = originalKey → request.left = body →
    request.right = universeValue → value = universeValue)

/-- The selected outer result retains the complete current public body-first node law. -/
theorem to_body_first_key_node_result [DecidableEq Symbol]
    (sourceName bodyId : Nat) (selectedKey originalKey : IntersectionFlatMemoKeyDomain.DomainKey)
    (body universeValue : Value Symbol Guard) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (actual : NodeResult sourceName bodyId selectedKey originalKey body universeValue request value) :
    SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
      sourceName bodyId selectedKey body universeValue request value := by
  exact actual.1

private theorem pattern_available_after_growth
    (before after : InternedConstructorTemplates.State Symbol Guard) (facts : Facts after)
    (growth : Grows before after) (pattern : Value Symbol Guard)
    (available : Available before pattern) (kind : tag pattern = 1 ∨ tag pattern = 3) :
    Available after pattern := by
  cases pattern with
  | node entry rows depth free =>
      exact facts.cached.nodes entry.key _ (growth.nodeRecords entry.key _ (available.resident entry rfl))
  | union entry members depth free =>
      exact facts.cached.nodes entry.key _ (growth.nodeRecords entry.key _ (available.resident entry rfl))
  | empty | reference | mu => simp [tag] at kind

private theorem reference_code [DecidableEq Symbol]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (chosen : decision domain.key (.reference (.interned name) : Value Symbol Guard)
      (.reference (.interned name)) = .leftReference) :
    compileNode (⟨domain, .reference (.interned name), .reference (.interned name)⟩ : NodeRequest Symbol Guard) =
      compileReference domain name (.reference (.interned name)) true := by
  simp only [compileNode, chosen]

private theorem reference_read_step
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other value : Value Symbol Guard) (current : SourceEqualityNativeDemand.State width)
    (bound : name ∈ names domain.key)
    (read : SourcePreparedSharedRows.read current.native.machine.heap name = some value) :
    SourceEqualityNativeDemand.step (.code (compileReference domain name other true)) current =
      .yielded (.code (requestNode domain value other)) current := by
  simp [compileReference, bound, SourceEqualityNativeDemand.step,
    SourceRecursiveIntersectionNative.step, read, SourceEqualityNativeDemand.lift]

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
    (actual : SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
      sourceName bodyId selectedKey body universeValue request value)
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

set_option maxHeartbeats 1800000 in
/-- Both warm query families retain all current key laws and the actual outer B/U result. -/
theorem query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (inputHeap : InternedConstructorTemplates.State Symbol Guard) (inputFacts : Facts inputHeap)
    (sourceGrowth : Grows sourceHeap inputHeap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available inputHeap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) (patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let bodyFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
        body universeValue bodyEntry.identity entry.identity
      ∀ (fuel : Nat),
      (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
        Physical before.native → Grows inputHeap before.native.machine.heap →
        SourceEqualityConstraintMemoAllocation.Valid before.operations →
        InputsThrough fuel (.code (.node request .pure)) before →
        FieldsThrough fuel (.code (.node request .pure)) before →
        Returned (NodeResult entry.identity bodyEntry.identity bodyFirst.1.key sourceDomain.1.key body universeValue) before.native.nodes → Returned (EdgeResult entry.identity bodyEntry.identity bodyFirst.1.key universeValue) before.native.edges →
        (Returned (NodeResult entry.identity bodyEntry.identity bodyFirst.1.key sourceDomain.1.key body universeValue) (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
          Returned (EdgeResult entry.identity bodyEntry.identity bodyFirst.1.key universeValue) (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
        ∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
          Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
          (NodeResult entry.identity bodyEntry.identity bodyFirst.1.key sourceDomain.1.key body universeValue) request value) ∧
      (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
        Physical before.native → Grows inputHeap before.native.machine.heap →
        SourceEqualityConstraintMemoAllocation.Valid before.operations →
        InputsThrough fuel (.code (.edge request .pure)) before →
        FieldsThrough fuel (.code (.edge request .pure)) before →
        Returned (NodeResult entry.identity bodyEntry.identity bodyFirst.1.key sourceDomain.1.key body universeValue) before.native.nodes → Returned (EdgeResult entry.identity bodyEntry.identity bodyFirst.1.key universeValue) before.native.edges →
        (Returned (NodeResult entry.identity bodyEntry.identity bodyFirst.1.key sourceDomain.1.key body universeValue) (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
          Returned (EdgeResult entry.identity bodyEntry.identity bodyFirst.1.key universeValue) (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
        ∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
          Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
          (EdgeResult entry.identity bodyEntry.identity bodyFirst.1.key universeValue) request value) := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored inputHeap inputFacts sourceGrowth domains cacheValid pattern patternAvailable patternClosed
      patternId patternIdentity patternKind
  obtain ⟨readEntry, readRows, readShape, readFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstReferenceRead.current_stored_universe_body_first_reference_read
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored inputHeap inputFacts sourceGrowth domains cacheValid pattern patternAvailable patternClosed
      patternId patternIdentity patternKind
  have sameEntry : readEntry = bodyEntry := (Value.node.inj (readShape.symm.trans bodyShape)).1
  have sameRows : readRows = bodyRows := (Value.node.inj (readShape.symm.trans bodyShape)).2.1
  subst readEntry
  subst readRows
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
    body universeValue bodyEntry.identity entry.identity
  dsimp only at sourceFacts readFacts
  have originalValid : Cache.Valid sourceDomain.2 :=
    (IntersectionEmptyDomain.make_correct domains cacheValid _).1
  have originalKey : sourceDomain.1.key = extend IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.bindings universeValue pattern).map Prod.fst)
      (pair entry.identity patternId) :=
    SourceRecursiveIntersectionSchedule.entered_key domains cacheValid IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
  have bodyKey : bodyFirst.1.key = extend sourceDomain.1.key
      ((SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst)
      (pair bodyEntry.identity entry.identity) :=
    SourceRecursiveIntersectionSchedule.entered_key sourceDomain.2 originalValid sourceDomain.1.key
      body universeValue bodyEntry.identity entry.identity
  have diagonalParts (first second owner : Nat) (same : pair first second = pair owner owner) :
      first = owner ∧ second = owner := by
    have lower := congrArg Prod.fst same
    have upper := congrArg Prod.snd same
    simp only [pair, Nat.min_self, Nat.max_self] at lower upper
    omega
  have freshBodyPair : pair bodyEntry.identity bodyEntry.identity ∉ bodyFirst.1.key.seen := by
    intro member
    rw [bodyKey] at member
    rcases (extend_seen _ _ _ _).mp member with same | previous
    · exact bodyApart (diagonalParts bodyEntry.identity entry.identity bodyEntry.identity same.symm).2.symm
    · rw [originalKey] at previous
      rcases (extend_seen _ _ _ _).mp previous with same | empty
      · exact bodyApart (diagonalParts entry.identity patternId bodyEntry.identity same.symm).1.symm
      · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at empty
  have sourceRows : InternedEdgeResidency.nodeEdges body = bodyRows := by
    rw [bodyShape]
    rfl
  have compiler : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = bodyFirst.1.key →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (InternedEdgeResidency.nodeEdges body) (InternedEdgeResidency.nodeEdges body) := by
    intro actualDomain sameKey
    have fresh : pair bodyEntry.identity bodyEntry.identity ∉ actualDomain.key.seen := by
      rw [sameKey]
      exact freshBodyPair
    have shaped : decision actualDomain.key
        (.node bodyEntry bodyRows 0 [.interned entry.identity])
        (.node bodyEntry bodyRows 0 [.interned entry.identity]) = .ordinary := by
      simp [decision, SourceRecursiveIntersectionControl.hasEmpty,
        SourceRecursiveIntersectionControl.reset, SourceRecursiveIntersectionControl.closedSelf,
        SourceRecursiveIntersectionControl.greater, SourceRecursiveIntersectionControl.compareValue,
        tag, identity, SourceRecursiveIntersectionControl.payload,
        Value.referenceOf, Value.free, fresh]
    have literalCompiled : compileNode ⟨actualDomain,
        .node bodyEntry bodyRows 0 [.interned entry.identity],
        .node bodyEntry bodyRows 0 [.interned entry.identity]⟩ = compileRows actualDomain bodyRows bodyRows := by
      simp only [compileNode, shaped]
    calc
      compileNode ⟨actualDomain, body, body⟩ = compileNode ⟨actualDomain,
          .node bodyEntry bodyRows 0 [.interned entry.identity],
          .node bodyEntry bodyRows 0 [.interned entry.identity]⟩ :=
        congrArg (fun value : Value Symbol Guard => compileNode ⟨actualDomain, value, value⟩) bodyShape
      _ = compileRows actualDomain bodyRows bodyRows := literalCompiled
      _ = compileRows actualDomain (InternedEdgeResidency.nodeEdges body)
          (InternedEdgeResidency.nodeEdges body) := by rw [sourceRows]
  have selected : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = bodyFirst.1.key →
      decision actualDomain.key universeValue referenceValue = .leftMu := by
    intro actualDomain sameKey
    rw [sameKey]
    exact sourceFacts.1
  have childPure : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = bodyFirst.1.key →
      ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current actualDomain.key
        universeValue referenceValue entry.identity entry.identity).1,
        SourceRecursiveIntersectionKernel.body universeValue,
        SourceRecursiveIntersectionKernel.body referenceValue⟩ =
        .pure (repeatedValue (pair bodyEntry.identity entry.identity)) := by
    intro actualDomain sameKey current currentValid
    rw [sameKey]
    exact (sourceFacts.2.2.2.1 current currentValid).2.2
  have absent : let binder := pair entry.identity entry.identity
      Reference.intersection binder.1 binder.2 ∉
        (repeatedValue (pair bodyEntry.identity entry.identity) : Value Symbol Guard).free :=
    sourceFacts.2.2.1
  have read : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = bodyFirst.1.key →
      ∀ current : SourceEqualityNativeDemand.State width,
      SourceCurrentAllocatedNativePhysicalCache.Valid current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨actualDomain, referenceValue, referenceValue⟩)) current =
        .yielded (.code (requestNode actualDomain universeValue referenceValue)) current := by
    intro actualDomain sameKey current physical currentGrowth
    have bound : entry.identity ∈ names actualDomain.key := by
      rw [sameKey]
      exact readFacts.1
    have referenceSelected : decision actualDomain.key referenceValue referenceValue = .leftReference := by
      rw [sameKey]
      exact readFacts.2.1
    have compiled : compileNode ⟨actualDomain, referenceValue, referenceValue⟩ =
        compileReference actualDomain entry.identity referenceValue true :=
      reference_code actualDomain entry.identity referenceSelected
    have sourceRead : SourcePreparedSharedRows.read current.native.machine.heap entry.identity =
        some universeValue := (readFacts.2.2.2 current physical.machine.1 currentGrowth).1
    exact (congrArg (fun code : Code Symbol Guard (Value Symbol Guard) =>
      SourceEqualityNativeDemand.step (.code code) current) compiled).trans
        (reference_read_step actualDomain entry.identity referenceValue universeValue current bound sourceRead)
  refine ⟨bodyEntry, bodyRows, bodyShape, ?_⟩
  dsimp only
  intro fuel
  refine SourceCurrentAllocatedNativeSourceQueryInduction.query_returned_and_raw_results
    (NodeResult entry.identity bodyEntry.identity bodyFirst.1.key sourceDomain.1.key body universeValue)
    (EdgeResult entry.identity bodyEntry.identity bodyFirst.1.key universeValue) inputHeap ?_ ?_ fuel
  · intro request before bodyState middle parentFuel bodySteps value next
      physical beforeGrowth valid plan fields entered firstBeforeGrowth _firstValid smaller actual nodeCalls edgeCalls
    have growth := InternedConstructorTemplates.grows_trans sourceGrowth beforeGrowth
    have firstGrowth := InternedConstructorTemplates.grows_trans sourceGrowth firstBeforeGrowth
    constructor
    · have oldCalls := fun child childNext childBefore childAfter used count childValue positive bounded origin childTrace =>
        (nodeCalls child childNext childBefore childAfter used count childValue positive bounded origin childTrace).1
      constructor
      · constructor
        · apply SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
            request before bodyState middle parentFuel bodySteps value next entered smaller actual
          intro childSteps _small childNext childValue childAfter childEntry childTrace closed
          exact (oldCalls ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.left⟩
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
          change domain.key = bodyFirst.1.key at atKey
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
              .pure (repeatedValue (pair bodyEntry.identity entry.identity)) :=
            childPure domain atKey bodyState.native.machine.domains reached.2.1.machine.2
          have observed := SourceCurrentAllocatedNativeRawMuCutoffReplay.left_mu_cutoff_trace_result
            ⟨domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
            before bodyState middle parentFuel bodySteps value (repeatedValue (pair bodyEntry.identity entry.identity))
            entry.identity entry.identity next (selected domain atKey) rfl rfl canonical absent
            entered smaller actual (by
              dsimp only
              intro used count positive bounded _small childNext childValue childAfter childEntry childTrace pure
              exact (oldCalls ⟨allocated.1,
                  SourceRecursiveIntersectionKernel.body (.mu entry body depth ordinary),
                  SourceRecursiveIntersectionKernel.body (.reference (.interned entry.identity))⟩
                childNext started childAfter used count childValue positive bounded childEntry childTrace).1.2
                  (repeatedValue (pair bodyEntry.identity entry.identity)) pure)
          exact observed.1
        · constructor
          · intro atKey leftSame rightSame
            rcases request with ⟨domain, left, right⟩
            change left = .reference (.interned entry.identity) at leftSame
            change right = .reference (.interned entry.identity) at rightSame
            subst left
            subst right
            change domain.key = bodyFirst.1.key at atKey
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
              (fun child => child = repeatedValue (pair bodyEntry.identity entry.identity)) next
              actualRead entered smaller actual (by
                intro used count positive bounded _small childNext childValue childAfter childEntry childTrace
                exact (oldCalls ⟨domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
                  childNext bodyState childAfter used count childValue positive bounded childEntry childTrace).2.1 atKey rfl rfl)
            exact observed.1
          · intro atKey leftSame rightSame
            rcases request with ⟨domain, left, right⟩
            change left = body at leftSame
            change right = body at rightSame
            subst left
            subst right
            change domain.key = bodyFirst.1.key at atKey
            have observed := SourceCurrentAllocatedNativeBodyFirstCoherentProductReplay.open_body_product_of_reference_row_traces
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              bodyEntry.identity entry.identity domain before bodyState middle parentFuel bodySteps value next
              (compiler domain atKey) physical growth valid plan fields entered smaller actual (by
                intro pair member childNext childBefore childAfter used count childValue
                  positive bounded origin childTrace
                have property := edgeCalls ⟨domain, pair.1, pair.2⟩ childNext childBefore childAfter
                  used count childValue positive bounded origin childTrace
                exact property.2 atKey)
            exact observed.1
    · intro atKey leftSame rightSame
      rcases request with ⟨domain, left, right⟩
      change left = body at leftSame
      change right = universeValue at rightSame
      subst left
      subst right
      have currentPattern : Available before.native.machine.heap pattern :=
        pattern_available_after_growth inputHeap before.native.machine.heap physical.machine.1
          beforeGrowth pattern patternAvailable patternKind
      obtain ⟨actualBodyEntry, actualBodyRows, actualBodyShape, _actualBodyApart, observed⟩ :=
        SourceCurrentAllocatedNativeSourceBodyFirstOuterReclosure.current_stored_universe_body_first_outer_body_reclosure
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          before bodyState middle physical growth domains cacheValid pattern currentPattern patternClosed patternId
          patternIdentity patternKind
      have entrySame : actualBodyEntry = bodyEntry :=
        (Value.node.inj (actualBodyShape.symm.trans bodyShape)).1
      have rowsSame : actualBodyRows = bodyRows :=
        (Value.node.inj (actualBodyShape.symm.trans bodyShape)).2.1
      subst actualBodyEntry
      subst actualBodyRows
      dsimp only at observed
      have completed := observed domain atKey parentFuel bodySteps value next plan entered smaller actual (by
        intro used count positive bounded _small childNext product childAfter origin actualKey childTrace
        let allocated := SourceRecursiveIntersectionEnvironment.enter bodyState.native.machine.domains domain.key
          body universeValue bodyEntry.identity entry.identity
        let started : Checked width :=
          {bodyState with native := advance bodyState.native {bodyState.native.machine with domains := allocated.2}}
        have property := nodeCalls ⟨allocated.1, body, body⟩ childNext started childAfter
          used count product positive bounded origin childTrace
        exact property.1.2.2.2 actualKey rfl rfl)
      exact completed.2.2.1
  · intro request before first middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered _firstGrowth firstValid smaller actual nodeCalls _edgeCalls
    have oldCalls := fun child childNext childBefore childAfter used count childValue positive bounded origin childTrace =>
      (nodeCalls child childNext childBefore childAfter used count childValue positive bounded origin childTrace).1
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
          have property := oldCalls ⟨request.domain, pair.1, pair.2⟩ childNext childBefore childAfter
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
          (repeatedValue (SourceRecursiveIntersectionControl.pair bodyEntry.identity entry.identity))
            ⟨request.domain, pair.1, pair.2⟩ selectedValue →
            result = selectedValue)
      request before first middle parentFuel bodySteps value next self sourceTop
      reached.2.1 firstValid entered smaller reached.2.2.2.2 actual (by
        intro used count positive bounded _small pair _member childNext childBefore childAfter childValue
          origin _childPhysical childTrace selectedValue known
        have property := oldCalls ⟨request.domain, pair.1, pair.2⟩ childNext childBefore childAfter
          used count childValue positive bounded origin childTrace
        exact known_result_at_key entry.identity bodyEntry.identity bodyFirst.1.key body (.mu entry body depth ordinary)
          ⟨request.domain, pair.1, pair.2⟩ childValue selectedValue property atKey known)
    have same := ordered_values
      (fun pair result => SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws.KnownResult
        ⟨request.domain, .mu entry body depth ordinary, .reference (.interned entry.identity)⟩
        ⟨request.domain, .reference (.interned entry.identity), .reference (.interned entry.identity)⟩
        (repeatedValue (SourceRecursiveIntersectionControl.pair bodyEntry.identity entry.identity))
        ⟨request.domain, pair.1, pair.2⟩ result) readback.1 selectedChildren
    exact ⟨same, by simpa only [same] using readback.2.1⟩

/-- Actual complete empty initialization retains both exact laws and each original raw query count. -/
theorem initial_node_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (inputHeap : InternedConstructorTemplates.State Symbol Guard) (inputFacts : Facts inputHeap)
    (sourceGrowth : Grows sourceHeap inputHeap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available inputHeap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) (patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let bodyFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
        body universeValue bodyEntry.identity entry.identity
      ∀ (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard),
      SourceRecursiveIntersectionKernel.Valid machine → Grows inputHeap machine.heap →
      ∀ (operations : SourceEqualityConstraintMemoAllocation.State),
      SourceEqualityConstraintMemoAllocation.Valid operations →
      ∀ (fuel : Nat) (request : NodeRequest Symbol Guard),
      let start : Checked width := ⟨initial width machine, operations⟩
      InputsThrough fuel (.code (.node request .pure)) start →
      FieldsThrough fuel (.code (.node request .pure)) start →
      (Returned (NodeResult entry.identity bodyEntry.identity bodyFirst.1.key sourceDomain.1.key body universeValue) (execute fuel (.code (.node request .pure)) start).state.native.nodes ∧
        Returned (EdgeResult entry.identity bodyEntry.identity bodyFirst.1.key universeValue) (execute fuel (.code (.node request .pure)) start).state.native.edges) ∧
      ∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) start (.code (.pure value)) after →
        (NodeResult entry.identity bodyEntry.identity bodyFirst.1.key sourceDomain.1.key body universeValue) request value := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, completed⟩ := query_returned_and_raw_results (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    inputHeap inputFacts sourceGrowth domains cacheValid pattern patternAvailable patternClosed patternId
    patternIdentity patternKind
  refine ⟨bodyEntry, bodyRows, bodyShape, ?_⟩
  dsimp only at completed ⊢
  intro machine machineValid inputGrowth operations operationsValid fuel request plan fields
  exact ((completed fuel).1 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid)
    inputGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty _)
    (SourceCurrentAllocatedNativeContextCache.returned_empty _))

/-- Actual complete empty initialization retains both exact laws and each original raw query count. -/
theorem initial_edge_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (inputHeap : InternedConstructorTemplates.State Symbol Guard) (inputFacts : Facts inputHeap)
    (sourceGrowth : Grows sourceHeap inputHeap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available inputHeap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) (patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let bodyFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
        body universeValue bodyEntry.identity entry.identity
      ∀ (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard),
      SourceRecursiveIntersectionKernel.Valid machine → Grows inputHeap machine.heap →
      ∀ (operations : SourceEqualityConstraintMemoAllocation.State),
      SourceEqualityConstraintMemoAllocation.Valid operations →
      ∀ (fuel : Nat) (request : EdgeRequest Symbol Guard),
      let start : Checked width := ⟨initial width machine, operations⟩
      InputsThrough fuel (.code (.edge request .pure)) start →
      FieldsThrough fuel (.code (.edge request .pure)) start →
      (Returned (NodeResult entry.identity bodyEntry.identity bodyFirst.1.key sourceDomain.1.key body universeValue) (execute fuel (.code (.edge request .pure)) start).state.native.nodes ∧
        Returned (EdgeResult entry.identity bodyEntry.identity bodyFirst.1.key universeValue) (execute fuel (.code (.edge request .pure)) start).state.native.edges) ∧
      ∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) start (.code (.pure value)) after →
        (EdgeResult entry.identity bodyEntry.identity bodyFirst.1.key universeValue) request value := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, completed⟩ := query_returned_and_raw_results (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    inputHeap inputFacts sourceGrowth domains cacheValid pattern patternAvailable patternClosed patternId
    patternIdentity patternKind
  refine ⟨bodyEntry, bodyRows, bodyShape, ?_⟩
  dsimp only at completed ⊢
  intro machine machineValid inputGrowth operations operationsValid fuel request plan fields
  exact ((completed fuel).2 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid)
    inputGrowth operationsValid plan fields
    (SourceCurrentAllocatedNativeContextCache.returned_empty _)
    (SourceCurrentAllocatedNativeContextCache.returned_empty _))

end MicroCFTA.SourceCurrentAllocatedNativeBodyFirstOuterQueryGlobalLaws
