import MicroCFTA.SourceCurrentAllocatedNativeDiagonalShortcutInputs

namespace MicroCFTA.SourceCurrentAllocatedNativeSourceRowIntegrationProbe
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (KnownResult)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (EdgeResult)
set_option autoImplicit false

example
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
      ∀ row ∈ bodyRows,
        ∀ (operations : SourceEqualityConstraintMemoAllocation.State)
          (_operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations) (fuel : Nat),
        let request : EdgeRequest Symbol Guard := ⟨diagonalTerminal.1, row, row⟩
        let start : SourceEqualityNativeDemand.State width :=
          ⟨SourceRecursiveIntersectionThunks.initial width machine, operations⟩
        InputsThrough fuel (.code (.edge request .pure)) start →
        FieldsThrough fuel (.code (.edge request .pure)) start →
        Returned EdgeResult (execute fuel (.code (.edge request .pure)) start).state.native.edges ∧
        ∀ (count : Nat) (result : EdgeValue Symbol Guard) (after : SourceEqualityNativeDemand.State width),
          count ≤ fuel → Steps count (.code (.edge request .pure)) start (.code (.pure result)) after →
          result.children = row.children.map (input (replacement (.interned entry.identity)
            (repeatedValue (pair entry.identity entry.identity)))) ∧
          result.entry.key = ⟨row.entry.key.symbol,
            (row.children.map (input (replacement (.interned entry.identity)
              (repeatedValue (pair entry.identity entry.identity))))).map Value.referenceOf,
            SourceEqualityConstraintConstructors.top⟩ := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, known⟩ :=
    SourceCurrentAllocatedNativeDiagonalShortcutInputs.current_stored_universe_diagonal_shortcut_inputs
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored machine.heap facts growth domains cacheValid pattern _patternAvailable _patternClosed
      patternId _patternIdentity _patternKind
  obtain ⟨classifiedEntry, marker, arrow, rows, classifiedShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      childKinds, _arrowPresent⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap facts growth
  have rowsSame : bodyRows = canonicalEdges (arrow :: rows) :=
    (Value.node.inj (bodyShape.symm.trans classifiedShape)).2.1
  refine ⟨bodyEntry, bodyRows, bodyShape, ?_⟩
  dsimp only
  intro row member operations operationsValid fuel plan fields
  have sourceTop := (childKinds row (by rw [← rowsSame]; exact member)).2.1
  have actual := SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.initial_edge_query_returned_and_raw_results
    machine machineValid operations operationsValid fuel _ plan fields
  refine ⟨actual.1.2, ?_⟩
  intro count result after bounded trace
  exact (actual.2 count result after bounded trace).2 rfl sourceTop _ (known row member)

end MicroCFTA.SourceCurrentAllocatedNativeSourceRowIntegrationProbe
