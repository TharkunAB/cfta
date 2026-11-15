import MicroCFTA.SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff
import MicroCFTA.InternedStoredSubstitutionScope
import MicroCFTA.InternedStoredSubstitutionRebind

/-!
# Ordered source body inputs at the body-first domain

Each original source row retains its ordered child positions.
The source substitution leaves the closed marker unchanged.
Each original reference has the prescribed body-first cutoff input.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstNonterminalRowInputs
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeReferenceTopRowQueryGlobalLaws (KnownResult)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

set_option maxHeartbeats 800000 in
/-- The actual source rows retain all prescribed inputs at the literal body-first domain. -/
theorem current_stored_universe_body_first_nonterminal_row_inputs
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
      let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        body universeValue bodyEntry.identity entry.identity
      let muTarget : NodeRequest Symbol Guard := ⟨bodyFirst.1, universeValue, referenceValue⟩
      let referenceTarget : NodeRequest Symbol Guard := ⟨bodyFirst.1, referenceValue, referenceValue⟩
      let cutoff : Value Symbol Guard := repeatedValue (pair bodyEntry.identity entry.identity)
      ∀ row ∈ bodyRows,
        All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
          KnownResult muTarget referenceTarget cutoff ⟨bodyFirst.1, children.1, children.2⟩ value)
          (row.children.zip row.children)
          (row.children.map (input (replacement (.interned entry.identity) cutoff))) := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, _sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
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
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    body universeValue bodyEntry.identity entry.identity
  let muTarget : NodeRequest Symbol Guard := ⟨bodyFirst.1, universeValue, referenceValue⟩
  let referenceTarget : NodeRequest Symbol Guard := ⟨bodyFirst.1, referenceValue, referenceValue⟩
  let cutoff : Value Symbol Guard := repeatedValue (pair bodyEntry.identity entry.identity)
  let environment : InternedStoredSubstitution.Environment Symbol Guard :=
    replacement (.interned entry.identity) cutoff
  have referenceInput : input environment (.reference (.interned entry.identity)) = cutoff := by
    simp [environment, input, replacement]
  change ∀ row ∈ bodyRows,
    All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
      KnownResult muTarget referenceTarget cutoff ⟨bodyFirst.1, children.1, children.2⟩ value)
      (row.children.zip row.children) (row.children.map (input environment))
  have bodyFirstMany (values : List (Value Symbol Guard)) :
      (∀ child ∈ values,
        KnownResult muTarget referenceTarget cutoff ⟨bodyFirst.1, child, child⟩ (input environment child)) →
      All₂ (fun (children : Value Symbol Guard × Value Symbol Guard) (value : Value Symbol Guard) =>
        KnownResult muTarget referenceTarget cutoff ⟨bodyFirst.1, children.1, children.2⟩ value)
        (values.zip values) (values.map (input environment)) := by
    induction values with
    | nil => intro _each; exact .nil
    | cons child tail ih =>
        intro each
        exact .cons (each child List.mem_cons_self)
          (ih (fun value member => each value (List.mem_cons_of_mem child member)))
  intro row member
  apply bodyFirstMany row.children
  intro child childMember
  have kinds := childKinds row (by rw [← rowsSame]; exact member)
  rcases kinds.2.2 child childMember with referenceCase | closedCase
  · subst child
    exact Or.inr ⟨Or.inr rfl, referenceInput⟩
  · exact Or.inl (Or.inl ⟨rfl, closedCase.2.2.1,
      InternedStoredSubstitutionScope.input_closed child environment closedCase.2.2.1⟩)

end MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstNonterminalRowInputs
