import MicroCFTA.SourceCurrentNativeOrderedOriginalEntry
import MicroCFTA.SourceSynthesisCurrentUniverseBodyChildClassification
import MicroCFTA.SourceSynthesisUniverseClosedResetSteps
import MicroCFTA.SourceCurrentAllocatedNativeClosedResetProfile
import MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
import MicroCFTA.SourceCurrentNativeEnterCommonOperand

/-!
# Original mixed-source child requests in the actual native row walk

The source body retains its reference and closed marker children.
Each ordinary operand child is shorter than the full original pattern.
Both row orders retain the literal original entered domain.
A checked child walk supplies availability at its actual call states.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSourceOrderedMixedOrdinaryChildQualification
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity tag)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniversePrefixHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

private theorem walk_qualified_calls
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (domain : Interned DomainKey) (qualified : Node × Node → Prop)
    {inputs : List (Node × Node)} {before after : Checked width} {values : List Node} {count : Nat}
    (actual : SourceCurrentAllocatedNativeSemanticTraceReadback.Walk
      (fun children : Node × Node => requestNode domain children.1 children.2)
      inputs before values after count)
    (each : ∀ children ∈ inputs, qualified children) :
    Language.All₂ (fun children value => qualified children ∧
      ∃ (childCount : Nat) (beforeChild afterChild : Checked width),
        Trace childCount (.code (requestNode domain children.1 children.2)) beforeChild
          (.code (.pure value)) afterChild ∧
        Domain beforeChild.native.machine domain ∧
        Available beforeChild.native.machine.heap children.1 ∧
        Available beforeChild.native.machine.heap children.2) inputs values := by
  induction actual with
  | nil => exact .nil
  | cons first rest before middle after value values firstCount restCount called tail ih =>
      have ready : NodeReady before.native.machine ⟨domain, first.1, first.2⟩ :=
        (SourceCurrentAllocatedNativeSemanticTraceReadback.current_inputs called).1
      exact .cons ⟨each first (List.mem_cons_self), firstCount, before, middle,
        called, ready.1, ready.2.1, ready.2.2⟩
        (ih (fun children member => each children (List.mem_cons_of_mem first member)))

/-- Actual source rows qualify both orders of every original mixed native child call. -/
theorem current_stored_universe_mixed_ordinary_child_qualification_ordered_entry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {Output : Type}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (pattern : Node) (_patternClosed : pattern.free = []) (patternId : Nat)
    (_patternIdentity : identity pattern = some patternId)
    (_patternKind : tag pattern = 1 ∨ tag pattern = 3) (universeFirst : Bool)
    (initial : Control Output) (start entryBefore enteredAfter : Checked width)
    (startPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (entryCount : Nat) (entryNext : Interned DomainKey → Code Symbol Guard Output)
    (entryPrefix : Trace entryCount initial start
      (.code (.enter IntersectionEmptyDomain.emptyDomain
        (if universeFirst then .mu entry body depth ordinary else pattern)
        (if universeFirst then pattern else .mu entry body depth ordinary)
        (if universeFirst then entry.identity else patternId)
        (if universeFirst then patternId else entry.identity) entryNext)) entryBefore) :
    let universeValue : Node := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
      IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
    Trace 1 (.code (.enter IntersectionEmptyDomain.emptyDomain
      (if universeFirst then universeValue else pattern)
      (if universeFirst then pattern else universeValue)
      (if universeFirst then entry.identity else patternId)
      (if universeFirst then patternId else entry.identity) entryNext)) entryBefore
      (.code (entryNext entered.1)) enteredAfter →
    Available entryBefore.native.machine.heap pattern ∧ Domain enteredAfter.native.machine entered.1 ∧
    entered.1.key.free.isEmpty = false ∧
    ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)) (marker : Node),
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      marker.free = [] ∧ InternedBoundaryAtoms.atoms marker = [] ∧
      ∀ (reader : Checked width), Physical reader.native →
      ∀ (operandEntry : Interned NodeKey) (operandRows : List (EdgeValue Symbol Guard))
        (operandDepth : Nat) (operandFree : List Reference),
        let operand : Node := .node operandEntry operandRows operandDepth operandFree
        Available reader.native.machine.heap operand → Profile entry.identity operand →
        height operand ≤ height pattern →
        ∀ bodyFirst : Bool,
        let leftRows := if bodyFirst then bodyRows else operandRows
        let rightRows := if bodyFirst then operandRows else bodyRows
        ∀ rowPair : EdgeValue Symbol Guard × EdgeValue Symbol Guard,
        rowPair ∈ SourceRecursiveIntersectionKernel.pairs leftRows rightRows →
        let inputs := rowPair.1.children.zip rowPair.2.children
        let qualified := fun children : Node × Node =>
          let sourceChild := if bodyFirst then children.1 else children.2
          let operandChild := if bodyFirst then children.2 else children.1
          (sourceChild = .reference (.interned entry.identity) ∨ sourceChild = marker) ∧
          Profile entry.identity operandChild ∧ height operandChild < height pattern ∧
          ((Profile entry.identity children.1 ∧ Profile entry.identity children.2) ∨
            (children.1 = .reference (.interned entry.identity) ∧
              Profile entry.identity children.2 ∧ height children.2 < height pattern) ∨
            (children.2 = .reference (.interned entry.identity) ∧
              Profile entry.identity children.1 ∧ height children.1 < height pattern))
        (∀ children ∈ inputs, qualified children) ∧
        ∀ (count : Nat) (after : Checked width) (values : List Node),
          Trace count (.code (walk (fun children : Node × Node =>
            requestNode entered.1 children.1 children.2) inputs)) reader (.code (.pure values)) after →
          Language.All₂ (fun children value => qualified children ∧
            ∃ (childCount : Nat) (beforeChild afterChild : Checked width),
              Trace childCount (.code (requestNode entered.1 children.1 children.2)) beforeChild
                (.code (.pure value)) afterChild ∧
              Domain beforeChild.native.machine entered.1 ∧
              Available beforeChild.native.machine.heap children.1 ∧
              Available beforeChild.native.machine.heap children.2) inputs values := by
  let universeValue : Node := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter entryBefore.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  dsimp only
  intro entryActual
  have entryPhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension entryPrefix startPhysical).1
  have entryReceipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary pattern _patternClosed patternId _patternIdentity _patternKind universeFirst
    entryNext 0 entryBefore enteredAfter (.code (entryNext entered.1)) entryPhysical entryActual
  obtain ⟨_allocatedEq, _enterStep, _entryChecked, _enterTail, _sameHeap, _sameDomains, _sameOperations,
    _universeBefore, patternAvailable, _universeAfter, _patternAfter, _allocatedDomain,
    enteredDomain, _enteredKey, nonempty, _afterPhysical, _enteredExtension, _identityAtReader⟩ := entryReceipt
  obtain ⟨bodyEntry, marker, arrow, rows, bodyShape, _bodyAvailable, _markerRead,
    _arrowChildren, _arrowKey, _catalog, markerClosed, _markerAvailable, markerAtoms,
    kinds, _arrowPresent⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap startPhysical.machine.1 sourceGrowth
  let bodyRows := canonicalEdges (arrow :: rows)
  have markerProfile : Profile entry.identity marker := by
    refine ⟨markerClosed, ?_⟩
    intro atom member
    rw [markerAtoms] at member
    cases member
  refine ⟨patternAvailable, enteredDomain, nonempty, bodyEntry, bodyRows, marker,
    bodyShape, markerClosed, markerAtoms, ?_⟩
  intro reader readerPhysical operandEntry operandRows operandDepth operandFree
  intro operandAvailable operandProfile bounded bodyFirst rowPair matched
  let inputs := rowPair.1.children.zip rowPair.2.children
  let qualified := fun children : Node × Node =>
    let sourceChild := if bodyFirst then children.1 else children.2
    let operandChild := if bodyFirst then children.2 else children.1
    (sourceChild = .reference (.interned entry.identity) ∨ sourceChild = marker) ∧
    Profile entry.identity operandChild ∧ height operandChild < height pattern ∧
    ((Profile entry.identity children.1 ∧ Profile entry.identity children.2) ∨
      (children.1 = .reference (.interned entry.identity) ∧
        Profile entry.identity children.2 ∧ height children.2 < height pattern) ∨
      (children.2 = .reference (.interned entry.identity) ∧
        Profile entry.identity children.1 ∧ height children.1 < height pattern))
  have rowChild (sourceRow : EdgeValue Symbol Guard) (sourceMember : sourceRow ∈ bodyRows)
      (operandRow : EdgeValue Symbol Guard) (operandMember : operandRow ∈ operandRows)
      (sourceChild : Node) (sourceIncluded : sourceChild ∈ sourceRow.children)
      (operandChild : Node) (operandIncluded : operandChild ∈ operandRow.children) :
      (sourceChild = .reference (.interned entry.identity) ∨ sourceChild = marker) ∧
      Profile entry.identity operandChild ∧ height operandChild < height pattern := by
    have inherited := SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms
      reader.native.machine.heap readerPhysical.machine.1 entry.identity
      operandEntry operandRows operandDepth operandFree operandAvailable
      operandProfile.1 operandProfile.2 operandRow operandMember operandChild operandIncluded
    have below := SourceSynthesisUniversePrefixHeight.child_lt
      operandEntry operandRows operandDepth operandFree operandRow operandMember operandChild operandIncluded
    refine ⟨?_, ⟨inherited.2.1, inherited.2.2⟩, Nat.lt_of_lt_of_le below bounded⟩
    rcases (kinds sourceRow sourceMember).2.2 sourceChild sourceIncluded with reference | markerChild
    · exact Or.inl reference
    · exact Or.inr markerChild.1
  have each : ∀ children ∈ inputs, qualified children := by
    intro children included
    have childMembers := List.of_mem_zip included
    cases bodyFirst with
    | false =>
        have rowMembers := (pairs_member operandRows bodyRows rowPair).mp matched
        have details := rowChild rowPair.2 rowMembers.2.1 rowPair.1 rowMembers.1
          children.2 childMembers.2 children.1 childMembers.1
        refine ⟨details.1, details.2.1, details.2.2, ?_⟩
        rcases details.1 with reference | markerChild
        · exact Or.inr (Or.inr ⟨reference, details.2.1, details.2.2⟩)
        · exact Or.inl ⟨details.2.1, by rw [markerChild]; exact markerProfile⟩
    | true =>
        have rowMembers := (pairs_member bodyRows operandRows rowPair).mp matched
        have details := rowChild rowPair.1 rowMembers.1 rowPair.2 rowMembers.2.1
          children.1 childMembers.1 children.2 childMembers.2
        refine ⟨details.1, details.2.1, details.2.2, ?_⟩
        rcases details.1 with reference | markerChild
        · exact Or.inr (Or.inl ⟨reference, details.2.1, details.2.2⟩)
        · exact Or.inl ⟨by rw [markerChild]; exact markerProfile, details.2.1⟩
  refine ⟨each, ?_⟩
  intro count after values actual
  exact walk_qualified_calls entered.1 qualified
    (SourceCurrentAllocatedNativeSemanticTraceReadback.walk_readback
      (fun children : Node × Node => requestNode entered.1 children.1 children.2)
      inputs count reader after values actual) each

end MicroCFTA.SourceCurrentAllocatedNativeSourceOrderedMixedOrdinaryChildQualification
