import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody
import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs
import MicroCFTA.SourceCurrentAllocatedNativeOpenBodyQueryGlobalLaws

/-!
# Initialized open body history from the original diagonal source

Original source facts supply the current-handle compiler and ordered inputs.
The same original body equations align all source witnesses.
Both complete memo laws retain the original machine, plans, and fuel.
Every bounded raw return has the exact open original-body product shape.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeDiagonalOpenBodyHistoryIntegrationProbe
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
open SourceCurrentAllocatedNativeOpenBodyQueryGlobalLaws (NodeResult ProductShape)
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (KnownResult EdgeResult)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
/-- The complete original source supplies initialized open-body history at every actual terminal-key handle. -/
theorem current_stored_universe_diagonal_open_body_results
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
      actualDomain.key = diagonalTerminal.1.key →
      ∀ (operations : SourceEqualityConstraintMemoAllocation.State)
        (_operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations) (fuel : Nat),
      let start : SourceEqualityNativeDemand.State width :=
        ⟨SourceRecursiveIntersectionThunks.initial width machine, operations⟩
      InputsThrough fuel (.code (.node ⟨actualDomain, body, body⟩ .pure)) start →
      FieldsThrough fuel (.code (.node ⟨actualDomain, body, body⟩ .pure)) start →
      Returned (NodeResult entry.identity entry.identity entry.identity diagonalTerminal.1.key body)
        (execute fuel (.code (.node ⟨actualDomain, body, body⟩ .pure)) start).state.native.nodes ∧
      Returned EdgeResult
        (execute fuel (.code (.node ⟨actualDomain, body, body⟩ .pure)) start).state.native.edges ∧
      ∀ (count : Nat) (result : Value Symbol Guard) (after : SourceEqualityNativeDemand.State width),
        count ≤ fuel →
        Steps count (.code (.node ⟨actualDomain, body, body⟩ .pure)) start (.code (.pure result)) after →
        ProductShape entry.identity entry.identity entry.identity body result := by
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
  have sameInputEntry : inputEntry = bodyEntry := (Value.node.inj (inputShape.symm.trans bodyShape)).1
  have sameInputRows : inputRows = bodyRows := (Value.node.inj (inputShape.symm.trans bodyShape)).2.1
  subst inputEntry
  subst inputRows
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    universeValue referenceValue entry.identity entry.identity
  let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
    body universeValue bodyEntry.identity entry.identity
  dsimp only at sourceFacts rowInputs
  obtain ⟨_bodyIdentity, _universeIdentity, _bodyOpen, _cutoffApart, _incomingFacts, terminalFacts⟩ :=
    sourceFacts
  have compiler : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = diagonalTerminal.1.key →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (nodeEdges body) (nodeEdges body) := by
    intro actualDomain sameKey
    exact (terminalFacts actualDomain sameKey).2.2
  have sourceRows : nodeEdges body = bodyRows := by
    rw [bodyShape]
    rfl
  have orderedInputs : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = diagonalTerminal.1.key → ∀ row ∈ nodeEdges body,
      All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
        KnownResult ⟨actualDomain, children.1, children.2⟩ value)
        (row.children.zip row.children)
        (row.children.map (input (replacement (.interned entry.identity)
          (repeatedValue (pair entry.identity entry.identity))))) := by
    intro actualDomain sameKey row member
    exact rowInputs actualDomain sameKey row (by rw [← sourceRows]; exact member)
  refine ⟨bodyEntry, bodyRows, bodyShape, ?_⟩
  dsimp only
  intro actualDomain sameKey operations operationsValid fuel plan fields
  have completed := SourceCurrentAllocatedNativeOpenBodyQueryGlobalLaws.initial_node_query_returned_and_raw_results
    (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    diagonalTerminal.1.key entry.identity entry.identity compiler orderedInputs
    machine machineValid growth operations operationsValid fuel ⟨actualDomain, body, body⟩ plan fields
  refine ⟨completed.1.1, completed.1.2, ?_⟩
  intro count result after bounded actual
  exact (completed.2 count result after bounded actual).2 sameKey rfl rfl

end MicroCFTA.SourceCurrentAllocatedNativeDiagonalOpenBodyHistoryIntegrationProbe
