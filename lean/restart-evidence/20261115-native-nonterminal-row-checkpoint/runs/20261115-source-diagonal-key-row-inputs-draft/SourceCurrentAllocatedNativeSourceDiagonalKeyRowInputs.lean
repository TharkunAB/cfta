import MicroCFTA.SourceCurrentAllocatedNativeDiagonalShortcutInputs

/-!
# Diagonal source inputs at the actual same-key domain

Every original body row retains its ordered child positions.
The closed marker remains unchanged under the source substitution.
The actual domain key selects the same pure diagonal cutoff.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
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

set_option autoImplicit false

private theorem repeated_code [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard) (cutoffKey : Nat × Nat)
    (chosen : decision request.domain.key request.left request.right = .repeated cutoffKey) :
    compileNode request = .pure (repeatedValue cutoffKey) := by
  simp only [compileNode, chosen]

set_option maxHeartbeats 800000 in
/-- The original source rows retain their exact inputs at every actual domain with the terminal key. -/
theorem current_stored_universe_diagonal_shortcut_inputs_at_same_key
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (_patternAvailable : Available heap pattern)
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
        ∀ row ∈ bodyRows,
          All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
            KnownResult ⟨actualDomain, children.1, children.2⟩ value)
            (row.children.zip row.children)
            (row.children.map (input (replacement (.interned entry.identity)
              (repeatedValue (pair entry.identity entry.identity))))) := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, sourceQueries⟩ :=
    SourceCurrentAllocatedNativeAuxiliaryCutoffQueries.current_stored_universe_auxiliary_cutoff_queries (width := width)
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern _patternAvailable _patternClosed patternId
      _patternIdentity _patternKind
  obtain ⟨classifiedEntry, marker, arrow, rows, classifiedShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      childKinds, _arrowPresent⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth
  have rowsSame : bodyRows = canonicalEdges (arrow :: rows) :=
    (Value.node.inj (bodyShape.symm.trans classifiedShape)).2.1
  refine ⟨bodyEntry, bodyRows, bodyShape, ?_⟩
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    universeValue referenceValue entry.identity entry.identity
  let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
    body universeValue bodyEntry.identity entry.identity
  let environment : InternedStoredSubstitution.Environment Symbol Guard :=
    replacement (.interned entry.identity) (repeatedValue (pair entry.identity entry.identity))
  dsimp only at sourceQueries
  have historicalSelected : decision diagonalTerminal.1.key referenceValue referenceValue =
      .repeated (pair entry.identity entry.identity) :=
    (sourceQueries ⟨diagonalTerminal.1, referenceValue, referenceValue⟩
      (pair entry.identity entry.identity) (Or.inr ⟨rfl, rfl⟩)).1
  have referenceInput : input environment (.reference (.interned entry.identity)) =
      repeatedValue (pair entry.identity entry.identity) := by
    simp [environment, input, replacement]
  change ∀ (actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
    actualDomain.key = diagonalTerminal.1.key →
      ∀ row ∈ bodyRows,
        All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
          KnownResult ⟨actualDomain, children.1, children.2⟩ value)
          (row.children.zip row.children) (row.children.map (input environment))
  intro actualDomain keySame
  have actualSelected : decision actualDomain.key referenceValue referenceValue =
      .repeated (pair entry.identity entry.identity) := by
    rw [keySame]
    exact historicalSelected
  have terminalPure : compileNode ⟨actualDomain, referenceValue, referenceValue⟩ =
      .pure (repeatedValue (pair entry.identity entry.identity)) :=
    repeated_code ⟨actualDomain, referenceValue, referenceValue⟩
      (pair entry.identity entry.identity) actualSelected
  have diagonalMany (values : List (Value Symbol Guard)) :
      (∀ child ∈ values, KnownResult ⟨actualDomain, child, child⟩ (input environment child)) →
      All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
        KnownResult ⟨actualDomain, children.1, children.2⟩ value)
        (values.zip values) (values.map (input environment)) := by
    induction values with
    | nil => intro _each; exact .nil
    | cons child tail ih =>
        intro each
        exact .cons (each child List.mem_cons_self)
          (ih (fun value member => each value (List.mem_cons_of_mem child member)))
  intro row member
  apply diagonalMany row.children
  intro child childMember
  have kinds := childKinds row (by rw [← rowsSame]; exact member)
  rcases kinds.2.2 child childMember with referenceCase | closedCase
  · subst child
    apply Or.inr
    rw [referenceInput]
    exact terminalPure
  · exact Or.inl ⟨rfl, closedCase.2.2.1,
      InternedStoredSubstitutionScope.input_closed child environment closedCase.2.2.1⟩

end MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalKeyRowInputs
