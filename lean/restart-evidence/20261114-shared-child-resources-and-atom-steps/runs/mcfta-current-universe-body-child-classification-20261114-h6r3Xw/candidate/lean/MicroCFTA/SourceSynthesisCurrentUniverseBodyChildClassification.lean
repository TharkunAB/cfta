-- UNCOMPILED SOURCE DRAFT. Root owns validation.
import MicroCFTA.SourceSynthesisCurrentUniverseAtomInductionSteps
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness

/-!
# Physical child requests below the same stored universe body

The original source rows retain their literal child positions.
Each body child is the original reference or the closed atomless marker.
Actual ordinary operand children are strict descendants of the original pattern.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The actual leaf marker has no recursive boundary atom. -/
private theorem marker_atomless (entry : Interned NodeKey) (row : EdgeValue Symbol Guard)
    (leaf : row.children = []) : atoms (.node entry [row] 0 []) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro atom occurrence
  simp only [atoms] at occurrence
  obtain ⟨edge, present, child, member, _⟩ := (edge_member [row] atom).mp occurrence
  have same : edge = row := List.mem_singleton.mp present
  subst edge
  rw [leaf] at member
  cases member

/-- The same stored source rows classify every actual child after record growth. -/
theorem current_stored_universe_body_physical_children_after_growth
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap) :
    ∃ (bodyEntry : Interned NodeKey) (marker : Value Symbol Guard)
      (arrow : EdgeValue Symbol Guard) (rows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity] ∧
      Available heap body ∧
      (∃ (markerEntry : Interned NodeKey) (markerRow : EdgeValue Symbol Guard),
        marker = .node markerEntry [markerRow] 0 [] ∧ markerRow.children = [] ∧
        markerRow.entry.key = ⟨literal "(->)", [], top⟩) ∧
      arrow.children = [marker, .reference (.interned entry.identity), .reference (.interned entry.identity)] ∧
      arrow.entry.key = ⟨literal "->",
        [marker.referenceOf, .ref (.interned entry.identity), .ref (.interned entry.identity)], top⟩ ∧
      Language.All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
        row.children = List.replicate descriptor.2 (.reference (.interned entry.identity)) ∧
        row.entry.key = ⟨literal descriptor.1,
          List.replicate descriptor.2 (.ref (.interned entry.identity)), top⟩)
        (SourceSynthesisUniverseBody.descriptors
          (SourceSynthesisCurrentContext.constructorCatalog lib query)) rows ∧
      marker.free = [] ∧ Available heap marker ∧ atoms marker = [] ∧
      (∀ row ∈ canonicalEdges (arrow :: rows), EdgeResident heap row ∧ row.entry.key.constraint = top ∧
        ∀ child ∈ row.children, child = .reference (.interned entry.identity) ∨
          (child = marker ∧ Available heap child ∧ child.free = [] ∧ atoms child = [])) ∧
      arrow ∈ canonicalEdges (arrow :: rows) := by
  obtain ⟨bodyEntry, marker, arrow, rows, bodyEq, markerRead, arrowChildren, arrowKey,
      catalog, markerClosed, _sourceMarkerAvailable, kinds, retained⟩ :=
    SourceSynthesisCurrentUniverseOwnership.current_stored_universe_rows
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
  have universeAvailable : Available heap (.mu entry body depth ordinary) :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have bodyAvailable : Available heap body :=
    universeAvailable.children body (by simp [InternedProbeProvenance.children])
  have actualBody : Available heap (.node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity]) := by
    rw [← bodyEq]
    exact bodyAvailable
  have markerAvailable : Available heap marker := by
    apply actualBody.children marker
    change marker ∈ (canonicalEdges (arrow :: rows)).flatMap EdgeValue.children
    exact List.mem_flatMap.mpr ⟨arrow, retained, by simp [arrowChildren]⟩
  obtain ⟨markerEntry, markerRow, markerEq, leaf, markerKey⟩ := markerRead
  have markerAtoms : atoms marker = [] := by
    rw [markerEq]
    exact marker_atomless markerEntry markerRow leaf
  refine ⟨bodyEntry, marker, arrow, rows, bodyEq, bodyAvailable,
    ⟨markerEntry, markerRow, markerEq, leaf, markerKey⟩, arrowChildren, arrowKey, catalog,
    markerClosed, markerAvailable, markerAtoms, ?_, retained⟩
  intro row present
  refine ⟨facts.linked bodyEntry.key _ (actualBody.resident bodyEntry rfl) row present,
    (kinds row present).1, ?_⟩
  intro child member
  rcases (kinds row present).2 child member with markerChild | referenceChild
  · right
    refine ⟨markerChild, ?_, ?_, ?_⟩
    · rw [markerChild]
      exact markerAvailable
    · rw [markerChild]
      exact markerClosed
    · rw [markerChild]
      exact markerAtoms
  · exact Or.inl referenceChild

/-- Actual child positions retain the original mixed domain and strict-descendant freshness. -/
theorem current_stored_universe_body_ordinary_child_requests_after_mixed_extension
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternAvailable : Available heap pattern)
    (patternClosed : pattern.free = []) (patternId : Nat)
    (patternIdentity : identity pattern = some patternId) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
    ∀ (operandEntry : Interned NodeKey) (operandRows : List (EdgeValue Symbol Guard))
      (operandDepth : Nat) (operandFree : List Reference),
      let operand : Value Symbol Guard := .node operandEntry operandRows operandDepth operandFree
      Available later.heap operand → operand.free = [] →
      (∀ atom ∈ atoms operand, atom = .mu entry.identity) → height operand ≤ height pattern →
      ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
        body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧ Available later.heap body ∧
        ∀ bodyRow ∈ bodyRows, ∀ operandRow ∈ operandRows,
          EdgeResident later.heap bodyRow ∧ EdgeResident later.heap operandRow ∧
          ∀ bodyChild ∈ bodyRow.children, ∀ operandChild ∈ operandRow.children,
            (bodyChild = .reference (.interned entry.identity) ∨
              (Available later.heap bodyChild ∧ bodyChild.free = [] ∧ atoms bodyChild = [])) ∧
            Available later.heap operandChild ∧ operandChild.free = [] ∧
            (∀ atom ∈ atoms operandChild, atom = .mu entry.identity) ∧
            height operandChild < height pattern ∧
            ∀ operandId : Nat, identity operandChild = some operandId →
              operandId ≠ patternId ∧ pair entry.identity operandId ≠ pair entry.identity patternId ∧
              pair operandId entry.identity ≠ pair entry.identity patternId ∧
              pair entry.identity operandId ∉ entered.1.key.seen ∧
              pair operandId entry.identity ∉ entered.1.key.seen ∧ Domain later entered.1 ∧
              SourceRecursiveIntersectionDomain.lookup later.heap entered.1.key entry.identity = some universeValue := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  obtain ⟨_universeClosed, originalFresh⟩ :=
    SourceSynthesisUniverseMixedDescendantFreshness.current_stored_universe_strict_descendant_fresh_after_mixed_entry
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern patternAvailable patternClosed patternId patternIdentity
  dsimp only
  intro later laterValid continuation operandEntry operandRows operandDepth operandFree
  dsimp only
  intro operandAvailable operandClosed operandAtoms bounded
  have laterGrowth : Grows sourceHeap later.heap := grows_trans growth continuation.heap
  obtain ⟨bodyEntry, marker, arrow, rows, bodyEq, bodyAvailable, _markerRead, _arrowChildren, _arrowKey,
      _catalog, _markerClosed, _markerAvailable, _markerAtoms, kinds, _retained⟩ :=
    current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      later.heap laterValid.1 laterGrowth
  refine ⟨bodyEntry, canonicalEdges (arrow :: rows), bodyEq, bodyAvailable, ?_⟩
  intro bodyRow bodyMember operandRow operandMember
  refine ⟨(kinds bodyRow bodyMember).1,
    laterValid.1.linked operandEntry.key _ (operandAvailable.resident operandEntry rfl) operandRow operandMember, ?_⟩
  intro bodyChild bodyIncluded operandChild operandIncluded
  have child := SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms
    later.heap laterValid.1 entry.identity operandEntry operandRows operandDepth operandFree
    operandAvailable operandClosed operandAtoms operandRow operandMember operandChild operandIncluded
  have below := SourceSynthesisUniversePrefixHeight.child_lt
    operandEntry operandRows operandDepth operandFree operandRow operandMember operandChild operandIncluded
  have strict : height operandChild < height pattern := Nat.lt_of_lt_of_le below bounded
  refine ⟨?_, child.1, child.2.1, child.2.2, strict, ?_⟩
  · rcases (kinds bodyRow bodyMember).2.2 bodyChild bodyIncluded with originalReference | markerChild
    · exact Or.inl originalReference
    · exact Or.inr markerChild.2
  · intro operandId operandIdentity
    exact originalFresh later laterValid continuation operandChild child.1 child.2.1
      operandId operandIdentity strict

end MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
