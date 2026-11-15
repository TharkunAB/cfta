import MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff
import MicroCFTA.SourcePreparedSharedRows

/-!
# Actual source reference read below the body-first domain

The source Mu selection excludes the diagonal repeated pair.
The body-first bindings retain the original universe name.
The actual current heap supplies the same complete stored universe value.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstReferenceRead
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

private theorem reference_code [DecidableEq Symbol]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (chosen : decision domain.key (.reference (.interned name) : Value Symbol Guard)
      (.reference (.interned name)) = .leftReference) :
    compileNode ⟨domain, .reference (.interned name), .reference (.interned name)⟩ =
      compileReference domain name (.reference (.interned name)) true := by
  simp only [compileNode, chosen]

set_option maxHeartbeats 800000 in
/-- The source body-first reference read retains the complete actual current state. -/
theorem current_stored_universe_body_first_reference_read
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
      entry.identity ∈ names bodyFirst.1.key ∧
      decision bodyFirst.1.key referenceValue referenceValue = .leftReference ∧
      compileNode ⟨bodyFirst.1, referenceValue, referenceValue⟩ =
        compileReference bodyFirst.1 entry.identity referenceValue true ∧
      (∀ (current : Checked width), Facts current.native.machine.heap →
        Grows sourceHeap current.native.machine.heap →
        SourcePreparedSharedRows.read current.native.machine.heap entry.identity = some universeValue ∧
        SourceEqualityNativeDemand.step
          (.code (compileNode ⟨bodyFirst.1, referenceValue, referenceValue⟩)) current =
          .yielded (.code (requestNode bodyFirst.1 universeValue referenceValue)) current) := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, muFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern _patternAvailable _patternClosed patternId
      _patternIdentity _patternKind
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    body universeValue bodyEntry.identity entry.identity
  dsimp only at muFacts
  have muSelected : decision bodyFirst.1.key universeValue referenceValue = .leftMu := muFacts.1
  have tagOrder : compare (2 : Nat) 4 = .lt := by decide
  have fresh : pair entry.identity entry.identity ∉ bodyFirst.1.key.seen := by
    intro seen
    have repeated : decision bodyFirst.1.key universeValue referenceValue =
        .repeated (pair entry.identity entry.identity) := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity,
        universeValue, referenceValue, Value.referenceOf, Value.free, seen, tagOrder]
    have impossible := muSelected.symm.trans repeated
    cases impossible
  have selected : decision bodyFirst.1.key referenceValue referenceValue = .leftReference := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      referenceValue, Value.referenceOf, Value.free, fresh,
      SourceRecursiveIntersectionSchedule.reference_interned]
  have compiled : compileNode ⟨bodyFirst.1, referenceValue, referenceValue⟩ =
      compileReference bodyFirst.1 entry.identity referenceValue true :=
    reference_code bodyFirst.1 entry.identity selected
  have originalValid : Cache.Valid original.2 :=
    (IntersectionEmptyDomain.make_correct domains cacheValid _).1
  have bodyKey : bodyFirst.1.key = extend original.1.key
      ((SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst)
      (pair bodyEntry.identity entry.identity) :=
    SourceRecursiveIntersectionSchedule.entered_key original.2 originalValid original.1.key
      body universeValue bodyEntry.identity entry.identity
  have bound : entry.identity ∈ names bodyFirst.1.key := by
    rw [bodyKey, extend_names]
    left
    simp [SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
      universeValue, bodyShape]
  refine ⟨bodyEntry, bodyRows, bodyShape, bound, selected, compiled, ?_⟩
  intro current currentFacts currentGrowth
  have universeAvailable : Available current.native.machine.heap universeValue :=
    currentFacts.cached.nodes key _ (currentGrowth.nodeRecords key _ stored)
  have read : SourcePreparedSharedRows.read current.native.machine.heap entry.identity = some universeValue :=
    SourcePreparedSharedRows.read_identity current.native.machine.heap currentFacts
      universeValue universeAvailable entry.identity rfl
  refine ⟨read, ?_⟩
  simp [compiled, compileReference, bound, SourceEqualityNativeDemand.step,
    SourceRecursiveIntersectionNative.step, read, SourceEqualityNativeDemand.lift]

end MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstReferenceRead
