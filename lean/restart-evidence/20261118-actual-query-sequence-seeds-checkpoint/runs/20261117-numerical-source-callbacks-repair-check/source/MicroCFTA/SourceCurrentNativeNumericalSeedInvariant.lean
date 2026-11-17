import MicroCFTA.SourceCurrentNativeWarmCMDefinitions
import MicroCFTA.SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws
import MicroCFTA.SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws
import MicroCFTA.InternedShallowHeap
import MicroCFTA.SourceCurrentNativeAuxiliaryBaseKeyRecovery

namespace MicroCFTA.SourceCurrentNativeNumericalSeedInvariant
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionDomain SourceRecursiveIntersectionControl
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Fixed-history initial laws from past numerical seeds]
Seeds is independent of the next root and full history horizon.
An actual entry supplies one joint key and identity-separation receipt.
Closed requests use the closed clause. Mixed requests use the singleton clause.
All edge children share the same domain. An empty zip uses the closed clause.
The past Seeds argument is an internal smaller-query induction hypothesis.
-/

def Seeds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (bodyId : Nat) (snapshot : Checked width) : Prop :=
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let baseKey := fun patternId : Nat =>
    extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId)
  InternedShallowHeap.NoNewMu sourceHeap snapshot.native.machine.heap ∧
  Returned (fun (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) =>
    ClosedQualified entry.identity request → Profile entry.identity value) snapshot.native.nodes ∧
  Returned (fun (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) =>
    (∀ pair ∈ request.left.children.zip request.right.children,
      ClosedQualified entry.identity ⟨request.domain, pair.1, pair.2⟩) →
    ∀ child ∈ row.children, Profile entry.identity child) snapshot.native.edges ∧
  Returned (fun (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) =>
    ∀ patternId : Nat, request.domain.key = baseKey patternId →
      Profile entry.identity value) snapshot.native.nodes ∧
  Returned (fun (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) =>
    ∀ patternId : Nat, request.domain.key = baseKey patternId →
      ∀ child ∈ row.children, Profile entry.identity child) snapshot.native.edges ∧
  ∀ patternId : Nat, patternId ≠ entry.identity → patternId ≠ bodyId →
    let bodyFirst := extend (baseKey patternId) [entry.identity] (pair bodyId entry.identity)
    let diagonalFirst := extend (baseKey patternId) [entry.identity] (pair entry.identity entry.identity)
    let diagonalTerminal := extend diagonalFirst [entry.identity] (pair bodyId entry.identity)
    Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
      entry.identity bodyId bodyFirst body universeValue) snapshot.native.nodes ∧
    Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
      entry.identity bodyId bodyFirst universeValue) snapshot.native.edges ∧
    Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
      entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue)
      snapshot.native.nodes ∧
    Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult snapshot.native.edges

private theorem authentic_numerical_key_and_identity_apart
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (wholeCount : Nat) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (bodyShape : body = .node bodyEntry bodyRows 0 [.interned entry.identity])
    (pattern : Value Symbol Guard) (patternId : Nat)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
      entry body depth ordinary pattern patternId domain) :
    domain.key = extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) ∧
      patternId ≠ entry.identity ∧ patternId ≠ bodyEntry.identity := by
  obtain ⟨closed, identified, kind, universeFirst, used, before, next, data⟩ := authentic
  dsimp only at data
  obtain ⟨_within, entryPrefix, _ordered, one, domainSame⟩ := data
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
    IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
  let after : Checked width :=
    {before with native := advance before.native {before.native.machine with domains := entered.2}}
  change domain = entered.1 at domainSame
  have beforePhysical :=
    (SourceCurrentNativeEnterCommonOperand.checked_trace_extension entryPrefix initialPhysical).1
  have receipt := SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands
    entry body depth ordinary pattern closed patternId identified kind universeFirst
    next 0 before after (.code (next entered.1)) beforePhysical one
  obtain ⟨_allocation, _step, _event, _tail, _heap, _domains, _operations,
    universeAvailable, patternAvailable, _universeAfter, _patternAfter, _startedDomain,
    _readerDomain, keyShape, _nonempty, _afterPhysical, _extension, _classify⟩ := receipt
  have shapedUniverse : Available before.native.machine.heap
      (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    rw [← bodyShape]
    exact universeAvailable
  have apart := SourceCurrentNativeAuxiliaryBaseKeyRecovery.source_parent_pair_avoids_auxiliary
    before.native.machine.heap beforePhysical.machine.1 entry bodyEntry bodyRows depth ordinary
    shapedUniverse pattern patternId patternAvailable closed identified kind
  have numbers : patternId ≠ entry.identity ∧ patternId ≠ bodyEntry.identity := by
    constructor
    · intro same
      exact apart.2 (congrArg (pair entry.identity) same)
    · intro same
      apply apart.1
      rw [same]
      exact Prod.ext (Nat.min_comm _ _) (Nat.max_comm _ _)
  refine ⟨?_, numbers⟩
  rw [domainSame]
  exact keyShape

theorem initial_payloads_for_actual_history_of_past_seeds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (fuel wholeCount : Nat) (rest : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) start)
    (actual : Trace wholeCount (.code (.node rootRequest .pure)) start rest reader)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId start) :
    (Returned (SourceCurrentNativeWarmCMDefinitions.NodeResult (width := width)
        rootRequest start wholeCount entry body depth ordinary) start.native.nodes ∧
      Returned (SourceCurrentNativeWarmCMDefinitions.EdgeResult (width := width)
        rootRequest start wholeCount entry body depth ordinary) start.native.edges) ∧
    ∀ (pattern : Value Symbol Guard) (patternId : Nat)
      (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
      AuthenticEntryAt (width := width) rootRequest start wholeCount
        entry body depth ordinary pattern patternId domain →
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let bodyFirst := extend domain.key [entry.identity] (pair bodyId entry.identity)
      let diagonalFirst := extend domain.key [entry.identity] (pair entry.identity entry.identity)
      let diagonalTerminal := extend diagonalFirst [entry.identity] (pair bodyId entry.identity)
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
        entry.identity bodyId bodyFirst body universeValue) start.native.nodes ∧
      Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
        entry.identity bodyId bodyFirst universeValue) start.native.edges ∧
      Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
        entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue)
        start.native.nodes ∧
      Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult start.native.edges := by
  classical
  have _retainedAdmissions := And.intro operationsValid
    (And.intro wholeBound (And.intro inputs (And.intro fields actual)))
  dsimp only [Seeds] at pastSeeds
  obtain ⟨_inventory, closedNodes, closedEdges, singletonNodes, singletonEdges, auxiliary⟩ := pastSeeds
  obtain ⟨bodyEntry, _marker, arrow, rows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  have actualBodyIdentity : identity body = some bodyEntry.identity := by
    rw [bodyShape]
    rfl
  have bodyIdEq : bodyEntry.identity = bodyId :=
    Option.some.inj (actualBodyIdentity.symm.trans bodyIdentity)
  have entryFacts (pattern : Value Symbol Guard) (patternId : Nat)
      (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
      (authentic : AuthenticEntryAt (width := width) rootRequest start wholeCount
        entry body depth ordinary pattern patternId domain) :
      domain.key = extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) ∧
        patternId ≠ entry.identity ∧ patternId ≠ bodyId := by
    have observed := authentic_numerical_key_and_identity_apart rootRequest start initialPhysical
      wholeCount entry body depth ordinary bodyEntry (canonicalEdges (arrow :: rows)) bodyShape
      pattern patternId domain authentic
    simpa only [bodyIdEq] using observed
  have mixedKey (request : NodeRequest Symbol Guard)
      (mixed : MixedQualifiedAt (width := width) rootRequest start wholeCount
        entry body depth ordinary request) :
      ∃ patternId : Nat, request.domain.key =
        extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) := by
    obtain ⟨pattern, patternId, _openAlias, _operand, authentic, _aliasKind, _operandProfile,
      _height, _strict, _ordered⟩ := mixed
    exact ⟨patternId, (entryFacts pattern patternId request.domain authentic).1⟩
  have initialNodes : Returned (SourceCurrentNativeWarmCMDefinitions.NodeResult (width := width)
      rootRequest start wholeCount entry body depth ordinary) start.native.nodes := by
    intro handle request value storedCell
    constructor
    · exact closedNodes handle request value storedCell
    · intro mixed
      obtain ⟨patternId, sameKey⟩ := mixedKey request mixed
      exact singletonNodes handle request value storedCell patternId sameKey
  have initialEdges : Returned (SourceCurrentNativeWarmCMDefinitions.EdgeResult (width := width)
      rootRequest start wholeCount entry body depth ordinary) start.native.edges := by
    intro handle request row storedCell qualifiedChildren
    by_cases allClosed : ∀ pair ∈ request.left.children.zip request.right.children,
        ClosedQualified entry.identity ⟨request.domain, pair.1, pair.2⟩
    · exact closedEdges handle request row storedCell allClosed
    · have hasMixed : ∃ pair : Value Symbol Guard × Value Symbol Guard,
          pair ∈ request.left.children.zip request.right.children ∧
          MixedQualifiedAt (width := width) rootRequest start wholeCount entry body depth ordinary
            ⟨request.domain, pair.1, pair.2⟩ := by
        by_contra none
        apply allClosed
        intro pair member
        rcases qualifiedChildren pair member with closed | mixed
        · exact closed
        · exact False.elim (none ⟨pair, member, mixed⟩)
      obtain ⟨pair, _member, mixed⟩ := hasMixed
      obtain ⟨patternId, sameKey⟩ := mixedKey ⟨request.domain, pair.1, pair.2⟩ mixed
      exact singletonEdges handle request row storedCell patternId sameKey
  refine ⟨⟨initialNodes, initialEdges⟩, ?_⟩
  intro pattern patternId domain authentic
  have observed := entryFacts pattern patternId domain authentic
  have selected := auxiliary patternId observed.2.1 observed.2.2
  simpa only [observed.1] using selected

end MicroCFTA.SourceCurrentNativeNumericalSeedInvariant

#print axioms MicroCFTA.SourceCurrentNativeNumericalSeedInvariant.initial_payloads_for_actual_history_of_past_seeds

#check MicroCFTA.SourceCurrentNativeNumericalSeedInvariant.Seeds
