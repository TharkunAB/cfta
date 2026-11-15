import MicroCFTA.SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalOuterReclosure
import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody
import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs
import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalKeyReferenceRead

/-!
# The actual outer source Mu result through warm native history

The old coherent result law remains a complete conjunct.
The original full pattern and source heap fix the added U/R clause.
Actual smaller child queries supply coherent B/R results.
The outer frame recloses full U at that same child endpoint.
Both complete empty initializations retain the original plans and fuel.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeDiagonalOuterQueryGlobalLaws
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
open SourceRecursiveIntersectionControl (identity tag decision repeatedValue pair)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

open SourceCurrentAllocatedNativeCoherentOpenBodyResult (ProductShape)

set_option autoImplicit false

def NodeResult [DecidableEq Symbol] (sourceName : Nat)
    (selectedKey firstKey originalKey : IntersectionFlatMemoKeyDomain.DomainKey)
    (body universeValue : Value Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
    sourceName sourceName sourceName selectedKey firstKey body universeValue request value ∧
  (request.domain.key = originalKey → request.left = universeValue →
    request.right = .reference (.interned sourceName) → value = universeValue)

/-- The new selected-parent clause retains every existing coherent node result. -/
theorem to_coherent_node_result [DecidableEq Symbol]
    (sourceName : Nat) (selectedKey firstKey originalKey : IntersectionFlatMemoKeyDomain.DomainKey)
    (body universeValue : Value Symbol Guard) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (actual : NodeResult sourceName selectedKey firstKey originalKey body universeValue request value) :
    SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
      sourceName sourceName sourceName selectedKey firstKey body universeValue request value := by
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

set_option maxHeartbeats 1800000 in
/-- Both warm query families preserve the old coherent clauses and the actual outer full-U result. -/
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
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
        universeValue referenceValue entry.identity entry.identity
      let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
        body universeValue bodyEntry.identity entry.identity
      ∀ (fuel : Nat),
      (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
        Physical before.native → Grows inputHeap before.native.machine.heap →
        SourceEqualityConstraintMemoAllocation.Valid before.operations →
        InputsThrough fuel (.code (.node request .pure)) before →
        FieldsThrough fuel (.code (.node request .pure)) before →
        Returned (NodeResult entry.identity diagonalTerminal.1.key diagonalFirst.1.key sourceDomain.1.key body universeValue) before.native.nodes → Returned EdgeResult before.native.edges →
        (Returned (NodeResult entry.identity diagonalTerminal.1.key diagonalFirst.1.key sourceDomain.1.key body universeValue) (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
          Returned EdgeResult (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
        ∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
          Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
          (NodeResult entry.identity diagonalTerminal.1.key diagonalFirst.1.key sourceDomain.1.key body universeValue) request value) ∧
      (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
        Physical before.native → Grows inputHeap before.native.machine.heap →
        SourceEqualityConstraintMemoAllocation.Valid before.operations →
        InputsThrough fuel (.code (.edge request .pure)) before →
        FieldsThrough fuel (.code (.edge request .pure)) before →
        Returned (NodeResult entry.identity diagonalTerminal.1.key diagonalFirst.1.key sourceDomain.1.key body universeValue) before.native.nodes → Returned EdgeResult before.native.edges →
        (Returned (NodeResult entry.identity diagonalTerminal.1.key diagonalFirst.1.key sourceDomain.1.key body universeValue) (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
          Returned EdgeResult (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
        ∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
          Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
          EdgeResult request value) := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody.current_stored_universe_diagonal_first_actual_mu_body
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored inputHeap inputFacts sourceGrowth domains cacheValid pattern patternAvailable patternClosed
      patternId patternIdentity patternKind
  obtain ⟨inputEntry, inputRows, inputShape, rowInputs⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs.current_stored_universe_diagonal_shortcut_inputs_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored inputHeap inputFacts sourceGrowth domains cacheValid pattern patternAvailable patternClosed
      patternId patternIdentity patternKind
  obtain ⟨readEntry, readRows, readShape, sourceRead⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyReferenceRead.current_stored_universe_diagonal_first_body_reference_read_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored inputHeap inputFacts sourceGrowth domains cacheValid pattern patternAvailable patternClosed
      patternId patternIdentity patternKind
  have sameInputEntry : inputEntry = bodyEntry := (Value.node.inj (inputShape.symm.trans bodyShape)).1
  have sameInputRows : inputRows = bodyRows := (Value.node.inj (inputShape.symm.trans bodyShape)).2.1
  subst inputEntry
  subst inputRows
  have sameReadEntry : readEntry = bodyEntry := (Value.node.inj (readShape.symm.trans bodyShape)).1
  have sameReadRows : readRows = bodyRows := (Value.node.inj (readShape.symm.trans bodyShape)).2.1
  subst readEntry
  subst readRows
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
    universeValue referenceValue entry.identity entry.identity
  let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
    body universeValue bodyEntry.identity entry.identity
  dsimp only at sourceFacts rowInputs sourceRead
  obtain ⟨bodyIdentity, _universeIdentity, _bodyOpen, cutoffApart, incomingFacts, terminalFacts⟩ :=
    sourceFacts
  have compiler : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = diagonalTerminal.1.key →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (InternedEdgeResidency.nodeEdges body) (InternedEdgeResidency.nodeEdges body) := by
    intro actualDomain sameKey
    exact (terminalFacts actualDomain sameKey).2.2
  have sourceRows : InternedEdgeResidency.nodeEdges body = bodyRows := by
    rw [bodyShape]
    rfl
  have orderedInputs : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = diagonalTerminal.1.key → ∀ row ∈ InternedEdgeResidency.nodeEdges body,
      All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
        KnownResult ⟨actualDomain, children.1, children.2⟩ value)
        (row.children.zip row.children)
        (row.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (pair entry.identity entry.identity))))) := by
    intro actualDomain sameKey row member
    exact rowInputs actualDomain sameKey row (by rw [← sourceRows]; exact member)
  have rightMu : ∀ actualIncoming : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualIncoming.key = diagonalFirst.1.key →
      decision actualIncoming.key body universeValue = .rightMu := by
    intro actualIncoming sameKey
    exact (incomingFacts actualIncoming sameKey).1
  have enteredKey : ∀ actualIncoming : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualIncoming.key = diagonalFirst.1.key →
      ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      (SourceRecursiveIntersectionEnvironment.enter current actualIncoming.key body universeValue
        bodyEntry.identity entry.identity).1.key = diagonalTerminal.1.key := by
    intro actualIncoming sameKey current currentValid
    exact (incomingFacts actualIncoming sameKey).2.2 current currentValid
  have pairedApart : pair bodyEntry.identity entry.identity ≠ pair entry.identity entry.identity :=
    fun same => cutoffApart same.symm
  have read : ∀ actualIncoming : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualIncoming.key = diagonalFirst.1.key →
      ∀ current : SourceEqualityNativeDemand.State width,
      SourceCurrentAllocatedNativePhysicalCache.Valid current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨actualIncoming, body, referenceValue⟩)) current =
        .yielded (.code (requestNode actualIncoming body universeValue)) current := by
    intro actualIncoming sameKey current physical currentGrowth
    exact ((sourceRead actualIncoming sameKey).2.2.2.2 current physical.machine.1 currentGrowth).2
  refine ⟨bodyEntry, bodyRows, bodyShape, ?_⟩
  dsimp only
  intro fuel
  refine SourceCurrentAllocatedNativeSourceQueryInduction.query_returned_and_raw_results
    (NodeResult entry.identity diagonalTerminal.1.key diagonalFirst.1.key sourceDomain.1.key
      body universeValue) EdgeResult inputHeap ?_ ?_ fuel
  · intro request before first middle parentFuel bodySteps value next
      physical beforeGrowth valid plan fields entered firstBeforeGrowth _firstValid smaller actual nodeCalls edgeCalls
    have growth := InternedConstructorTemplates.grows_trans sourceGrowth beforeGrowth
    have firstGrowth := InternedConstructorTemplates.grows_trans sourceGrowth firstBeforeGrowth
    constructor
    · have oldCalls := fun child childNext childBefore childAfter used count childValue positive bounded origin childTrace =>
        (nodeCalls child childNext childBefore childAfter used count childValue positive bounded origin childTrace).1
      constructor
      · constructor
        · constructor
          · constructor
            · apply SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
                request before first middle parentFuel bodySteps value next entered smaller actual
              intro childSteps _small childNext childValue childAfter childEntry childTrace closed
              exact (oldCalls ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.left⟩
                childNext first childAfter 1 childSteps childValue (by decide) (by omega)
                childEntry childTrace).1.1.1.1 rfl closed
            · exact SourceCurrentAllocatedNativePureQueryLaw.raw_result
                request first middle bodySteps value actual
          · intro keySame leftSame rightSame
            rcases request with ⟨domain, left, right⟩
            change left = body at leftSame
            change right = body at rightSame
            subst left
            subst right
            change domain.key = diagonalTerminal.1.key at keySame
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
              entry.identity entry.identity domain before first middle parentFuel bodySteps value next
              (compiler domain keySame) physical growth valid plan fields entered smaller actual (by
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
                        (repeatedValue (SourceRecursiveIntersectionControl.pair entry.identity entry.identity))))) := by
                  rw [← self]
                  exact orderedInputs domain keySame pair.1 sourceMember.1
                exact property.2 self.symm (sourceTop pair.1 sourceMember.1) _ selectedInputs)
            obtain ⟨productEntry, products, _rawRows, _workMiddle, _count, _bounded, aligned, _retained,
                _middlePhysical, _middleExtension, _middleResident, _throughWork, _resultEq, _afterEq,
                _canonical, nodeRead, afterPhysical, _afterExtension, _originalExtension, _afterGrowth,
                _available, afterResident, _reclosed, _optionalStep, _optionalDone⟩ := observed
            have functional := SourceCurrentAllocatedNativeCoherentOpenBodyResult.identity_functional_of_resident
              middle.native.machine.heap afterPhysical.machine.1 products afterResident
            exact ⟨productEntry, products, aligned, functional, nodeRead⟩
        · intro keySame leftSame rightSame
          rcases request with ⟨domain, left, right⟩
          change left = body at leftSame
          change right = .mu entry body depth ordinary at rightSame
          subst left
          subst right
          change domain.key = diagonalFirst.1.key at keySame
          have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
            parentFuel 1 (.code (.node ⟨domain, body, .mu entry body depth ordinary⟩ .pure))
            (.code (compileNode ⟨domain, body, .mu entry body depth ordinary⟩)) next
            before first physical plan entered (by omega)
          obtain ⟨_bodyEntry, _marker, _arrow, _rows, bodyShape, _bodyFacts⟩ :=
            SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              before.native.machine.heap physical.machine.1 growth
          have bodyFixed : SourceRecursiveIntersectionKernel.body body = body := by
            rw [bodyShape]
            rfl
          let allocated := SourceRecursiveIntersectionEnvironment.enter first.native.machine.domains domain.key
            body (.mu entry body depth ordinary) bodyEntry.identity entry.identity
          let started : Checked width :=
            {first with native := advance first.native {first.native.machine with domains := allocated.2}}
          have actualChildKey : allocated.1.key = diagonalTerminal.1.key :=
            enteredKey domain keySame first.native.machine.domains reached.2.1.machine.2
          have unused : ∀ child, ProductShape entry.identity entry.identity entry.identity body child →
              Reference.intersection (pair bodyEntry.identity entry.identity).1 (pair bodyEntry.identity entry.identity).2 ∉ child.free := by
            intro child shape member
            have weak := SourceCurrentAllocatedNativeCoherentOpenBodyResult.to_product_shape
              entry.identity entry.identity entry.identity body child shape
            obtain ⟨_productEntry, _products, _aligned, same⟩ := weak
            rw [same] at member
            have components := Reference.intersection.inj (List.mem_singleton.mp member)
            exact pairedApart (Prod.ext components.1 components.2)
          have observed := SourceCurrentAllocatedNativeRawRightMuUnusedReplay.right_mu_unused_trace_result
            (ProductShape entry.identity entry.identity entry.identity body)
            ⟨domain, body, .mu entry body depth ordinary⟩ before first middle parentFuel bodySteps value
            bodyEntry.identity entry.identity next (rightMu domain keySame) bodyIdentity rfl unused entered smaller actual (by
              dsimp only
              intro used count positive bounded _small childNext childValue childAfter childEntry childTrace
              have property := oldCalls ⟨allocated.1, SourceRecursiveIntersectionKernel.body body,
                  SourceRecursiveIntersectionKernel.body (.mu entry body depth ordinary)⟩
                childNext started childAfter used count childValue positive bounded childEntry childTrace
              exact property.1.1.2 actualChildKey bodyFixed rfl)
          exact observed.1
      · intro keySame leftSame rightSame
        rcases request with ⟨domain, left, right⟩
        change left = body at leftSame
        change right = .reference (.interned entry.identity) at rightSame
        subst left
        subst right
        change domain.key = diagonalFirst.1.key at keySame
        have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
          parentFuel 1 (.code (.node ⟨domain, body, .reference (.interned entry.identity)⟩ .pure))
          (.code (compileNode ⟨domain, body, .reference (.interned entry.identity)⟩)) next
          before first physical plan entered (by omega)
        have actualRead := read domain keySame first reached.2.1 firstGrowth
        have observed := SourceCurrentAllocatedNativeRawReferencePredicateReplay.reference_trace_predicate_of_actual_read
          ⟨domain, body, .reference (.interned entry.identity)⟩
          ⟨domain, body, .mu entry body depth ordinary⟩ before first middle parentFuel bodySteps value
          (ProductShape entry.identity entry.identity entry.identity body) next
          actualRead entered smaller actual (by
            intro used count positive bounded _small childNext childValue childAfter childEntry childTrace
            have property := oldCalls ⟨domain, body, .mu entry body depth ordinary⟩
              childNext first childAfter used count childValue positive bounded childEntry childTrace
            exact property.1.2 keySame rfl rfl)
        exact observed.1
    · intro keySame leftSame rightSame
      rcases request with ⟨domain, left, right⟩
      change left = universeValue at leftSame
      change right = .reference (.interned entry.identity) at rightSame
      subst left
      subst right
      have currentPattern : Available before.native.machine.heap pattern :=
        pattern_available_after_growth inputHeap before.native.machine.heap physical.machine.1
          beforeGrowth pattern patternAvailable patternKind
      have observed :=
        SourceCurrentAllocatedNativeSourceDiagonalOuterReclosure.current_stored_universe_diagonal_outer_body_reclosure
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          before first middle physical growth domains cacheValid pattern currentPattern patternClosed patternId
          patternIdentity patternKind
      dsimp only at observed
      have completed := observed domain keySame parentFuel bodySteps value next plan entered smaller actual (by
        intro used count positive bounded _small childNext product childAfter origin actualKey childTrace
        let allocated := SourceRecursiveIntersectionEnvironment.enter first.native.machine.domains domain.key
          universeValue (.reference (.interned entry.identity)) entry.identity entry.identity
        let started : Checked width :=
          {first with native := advance first.native {first.native.machine with domains := allocated.2}}
        have property := nodeCalls ⟨allocated.1, body, .reference (.interned entry.identity)⟩
          childNext started childAfter used count product positive bounded origin childTrace
        exact property.1.2 actualKey rfl rfl)
      exact completed.2.2.1
  · intro request before first middle parentFuel bodySteps value next
      physical _growth _valid plan _fields entered _firstGrowth firstValid smaller actual nodeCalls _edgeCalls
    have oldCalls := fun child childNext childBefore childAfter used count childValue positive bounded origin childTrace =>
      (nodeCalls child childNext childBefore childAfter used count childValue positive bounded origin childTrace).1
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
          have property := oldCalls ⟨request.domain, pair.1, pair.2⟩ childNext childBefore childAfter
            used count childValue positive bounded origin childTrace
          exact known_result ⟨request.domain, pair.1, pair.2⟩ childValue wanted property.1.1.1 known)
      have same := ordered_values request.domain readback.1 selected
      exact ⟨same, by simpa only [same] using readback.2.1⟩

/-- The actual complete empty initialization preserves both laws and every bounded raw result. -/
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
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
        universeValue referenceValue entry.identity entry.identity
      let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
        body universeValue bodyEntry.identity entry.identity
      ∀ (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard),
      SourceRecursiveIntersectionKernel.Valid machine → Grows inputHeap machine.heap →
      ∀ (operations : SourceEqualityConstraintMemoAllocation.State),
      SourceEqualityConstraintMemoAllocation.Valid operations →
      ∀ (fuel : Nat) (request : NodeRequest Symbol Guard),
      let start : Checked width := ⟨initial width machine, operations⟩
      InputsThrough fuel (.code (.node request .pure)) start →
      FieldsThrough fuel (.code (.node request .pure)) start →
      (Returned (NodeResult entry.identity diagonalTerminal.1.key diagonalFirst.1.key sourceDomain.1.key body universeValue) (execute fuel (.code (.node request .pure)) start).state.native.nodes ∧
        Returned EdgeResult (execute fuel (.code (.node request .pure)) start).state.native.edges) ∧
      ∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) start (.code (.pure value)) after →
        (NodeResult entry.identity diagonalTerminal.1.key diagonalFirst.1.key sourceDomain.1.key body universeValue) request value := by
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

/-- The actual complete empty initialization preserves both laws and every bounded raw result. -/
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
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let sourceDomain := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter sourceDomain.2 sourceDomain.1.key
        universeValue referenceValue entry.identity entry.identity
      let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
        body universeValue bodyEntry.identity entry.identity
      ∀ (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard),
      SourceRecursiveIntersectionKernel.Valid machine → Grows inputHeap machine.heap →
      ∀ (operations : SourceEqualityConstraintMemoAllocation.State),
      SourceEqualityConstraintMemoAllocation.Valid operations →
      ∀ (fuel : Nat) (request : EdgeRequest Symbol Guard),
      let start : Checked width := ⟨initial width machine, operations⟩
      InputsThrough fuel (.code (.edge request .pure)) start →
      FieldsThrough fuel (.code (.edge request .pure)) start →
      (Returned (NodeResult entry.identity diagonalTerminal.1.key diagonalFirst.1.key sourceDomain.1.key body universeValue) (execute fuel (.code (.edge request .pure)) start).state.native.nodes ∧
        Returned EdgeResult (execute fuel (.code (.edge request .pure)) start).state.native.edges) ∧
      ∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) start (.code (.pure value)) after →
        EdgeResult request value := by
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

end MicroCFTA.SourceCurrentAllocatedNativeDiagonalOuterQueryGlobalLaws
