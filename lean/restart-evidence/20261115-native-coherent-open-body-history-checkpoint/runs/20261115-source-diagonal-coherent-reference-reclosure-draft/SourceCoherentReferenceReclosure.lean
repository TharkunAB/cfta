import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody
import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs
import MicroCFTA.SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalKeyReferenceRead
import MicroCFTA.SourceCurrentAllocatedNativePrefixOperations
import MicroCFTA.SourceCurrentNativeOpenRequestResults

/-!
# Same-state source reclosure after initialized coherent reference history

Original source facts supply the actual full-U read, Mu entry, and ordered inputs.
The same original body equations align all source witnesses.
Both complete memo laws retain the original machine, plans, and fuel.
Every bounded B/R raw return recloses to full U at its actual returned state.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeDiagonalCoherentReferenceReclosureProbe
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws (NodeResult)
open SourceCurrentAllocatedNativeCoherentOpenBodyResult (ProductShape)
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (KnownResult EdgeResult)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
/-- Every actual original-budget reference return recloses full U at the same complete state. -/
theorem current_stored_universe_diagonal_coherent_reference_reclosure
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (facts : Facts machine.heap) (growth : Grows sourceHeap machine.heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (_patternAvailable : Available machine.heap pattern)
    (_patternClosed : pattern.free = []) (patternId : Nat)
    (_patternIdentity : identity pattern = some patternId)
    (_patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        universeValue referenceValue entry.identity entry.identity
      let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
        body universeValue bodyEntry.identity entry.identity
      ∀ (actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
      actualDomain.key = diagonalFirst.1.key →
      ∀ (operations : SourceEqualityConstraintMemoAllocation.State)
        (_operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations) (fuel : Nat),
      let start : SourceEqualityNativeDemand.State width :=
        ⟨SourceRecursiveIntersectionThunks.initial width machine, operations⟩
      InputsThrough fuel (.code (.node ⟨actualDomain, body, referenceValue⟩ .pure)) start →
      FieldsThrough fuel (.code (.node ⟨actualDomain, body, referenceValue⟩ .pure)) start →
      Returned (NodeResult entry.identity entry.identity entry.identity diagonalTerminal.1.key
        diagonalFirst.1.key body universeValue)
        (execute fuel (.code (.node ⟨actualDomain, body, referenceValue⟩ .pure)) start).state.native.nodes ∧
      Returned EdgeResult
        (execute fuel (.code (.node ⟨actualDomain, body, referenceValue⟩ .pure)) start).state.native.edges ∧
      ∀ (count : Nat) (result : Value Symbol Guard) (after : SourceEqualityNativeDemand.State width),
        count ≤ fuel →
        Steps count (.code (.node ⟨actualDomain, body, referenceValue⟩ .pure)) start (.code (.pure result)) after →
        ProductShape entry.identity entry.identity entry.identity body result ∧
        SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity entry.identity) result
          after.native.machine.heap = .done universeValue after.native.machine.heap ∧
        SourceEqualityNativeDemand.step
          (.code (.optionalBinder (pair entry.identity entry.identity) result .pure)) after =
          .yielded (.code (.pure universeValue)) after ∧
        SourceEqualityNativeDemand.execute 2
          (.code (.optionalBinder (pair entry.identity entry.identity) result .pure)) after =
          .done universeValue after := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody.current_stored_universe_diagonal_first_actual_mu_body
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored machine.heap facts growth domains cacheValid pattern _patternAvailable _patternClosed
      patternId _patternIdentity _patternKind
  obtain ⟨inputEntry, inputRows, inputShape, rowInputs⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs.current_stored_universe_diagonal_shortcut_inputs_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored machine.heap facts growth domains cacheValid pattern _patternAvailable _patternClosed
      patternId _patternIdentity _patternKind
  obtain ⟨readEntry, readRows, readShape, sourceRead⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalKeyReferenceRead.current_stored_universe_diagonal_first_body_reference_read_at_same_key
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored machine.heap facts growth domains cacheValid pattern _patternAvailable _patternClosed
      patternId _patternIdentity _patternKind
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
  let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
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
  intro actualDomain sameKey operations operationsValid fuel plan fields
  have completed := SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.initial_node_query_returned_and_raw_results
    (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    diagonalTerminal.1.key entry.identity entry.identity compiler orderedInputs
    diagonalFirst.1.key bodyEntry.identity rightMu bodyIdentity enteredKey pairedApart read
    machine machineValid growth operations operationsValid fuel ⟨actualDomain, body, referenceValue⟩ plan fields
  refine ⟨completed.1.1, completed.1.2, ?_⟩
  intro count result after bounded actual
  have shape := (completed.2 count result after bounded actual).2 sameKey rfl rfl
  let request : NodeRequest Symbol Guard := ⟨actualDomain, body, referenceValue⟩
  let start : SourceEqualityNativeDemand.State width :=
    ⟨SourceRecursiveIntersectionThunks.initial width machine, operations⟩
  have physical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native :=
    SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid
  have reached := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    fuel count (.code (.node request .pure)) (.code (.pure result)) .pure start after sourceHeap
    physical plan fields operationsValid growth actual bounded
  have available : Available after.native.machine.heap result :=
    SourceCurrentNativeOpenRequestResults.node_result count request start after result physical reached.1
  have reclosed := SourceCurrentAllocatedNativeCoherentOpenBodyResult.stored_open_product_optional_reclosure
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    after reached.2.1.machine.1 reached.2.2.2.1 entry.identity entry.identity result available shape
  exact ⟨shape, reclosed⟩

end MicroCFTA.SourceCurrentAllocatedNativeDiagonalCoherentReferenceReclosureProbe
