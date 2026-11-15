import MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstReferenceRead

/-!
# Actual body/reference read below the diagonal-first domain

The original source fixes the full open body record.
The new diagonal pair retains the original source pair.
Both pairs differ from the body/universe pair.
The right reference reads the full original universe value.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalFirstBodyReferenceRead
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

private theorem closed_record_reference (value : Value Symbol Guard) (closed : value.free = [])
    (name : Nat) (identified : identity value = some name) :
    SourcePreparedSharedRows.reference value = some name := by
  cases value with
  | empty => simp only [identity, reduceCtorEq] at identified
  | reference own => simp only [Value.free, List.cons_ne_self] at closed
  | node | mu | union =>
      simpa only [identity, SourcePreparedSharedRows.reference] using identified

private theorem reference_code [DecidableEq Symbol]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other : Value Symbol Guard)
    (chosen : decision domain.key other (.reference (.interned name)) = .rightReference) :
    compileNode (⟨domain, other, .reference (.interned name)⟩ : NodeRequest Symbol Guard) =
      compileReference domain name other false := by
  simp only [compileNode, chosen]

private theorem reference_read_step
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other value : Value Symbol Guard) (current : Checked width)
    (bound : name ∈ names domain.key)
    (read : SourcePreparedSharedRows.read current.native.machine.heap name = some value) :
    SourceEqualityNativeDemand.step (.code (compileReference domain name other false)) current =
      .yielded (.code (requestNode domain other value)) current := by
  simp [compileReference, bound, SourceEqualityNativeDemand.step,
    SourceRecursiveIntersectionNative.step, read, SourceEqualityNativeDemand.lift]

set_option maxHeartbeats 1200000 in
/-- The source diagonal-first right-reference read retains the complete actual current state. -/
theorem current_stored_universe_diagonal_first_body_reference_read
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
      entry.identity ∈ names diagonalFirst.1.key ∧
      pair bodyEntry.identity entry.identity ∉ diagonalFirst.1.key.seen ∧
      decision diagonalFirst.1.key body referenceValue = .rightReference ∧
      compileNode ⟨diagonalFirst.1, body, referenceValue⟩ =
        compileReference diagonalFirst.1 entry.identity body false ∧
      (∀ (current : Checked width), Facts current.native.machine.heap →
        Grows sourceHeap current.native.machine.heap →
        SourcePreparedSharedRows.read current.native.machine.heap entry.identity = some universeValue ∧
        SourceEqualityNativeDemand.step
          (.code (compileNode ⟨diagonalFirst.1, body, referenceValue⟩)) current =
          .yielded (.code (requestNode diagonalFirst.1 body universeValue)) current) := by

  obtain ⟨bodyEntry, bodyRows, bodyShape, _sourceQueries⟩ :=
    SourceCurrentAllocatedNativeAuxiliaryCutoffQueries.current_stored_universe_auxiliary_cutoff_queries
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern _patternAvailable _patternClosed patternId
      _patternIdentity _patternKind
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    universeValue referenceValue entry.identity entry.identity
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have bodyAvailable : Available heap body :=
    universeAvailable.children body (by simp [InternedProbeProvenance.children, universeValue])
  have bodyApart : bodyEntry.identity ≠ entry.identity := by
    apply SourceSynthesisUniverseBodyReferenceControl.body_identity_ne
      entry bodyEntry bodyRows depth ordinary ⟨heap, domains⟩ facts
    change Available heap (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary)
    rw [← bodyShape]
    exact universeAvailable
  have bodyRead : SourcePreparedSharedRows.read heap bodyEntry.identity = some body :=
    SourcePreparedSharedRows.read_identity heap facts body bodyAvailable bodyEntry.identity (by rw [bodyShape]; rfl)
  have patternRead : SourcePreparedSharedRows.read heap patternId = some pattern :=
    SourcePreparedSharedRows.read_identity heap facts pattern _patternAvailable patternId
      (closed_record_reference pattern _patternClosed patternId _patternIdentity)
  have bodyPatternApart : bodyEntry.identity ≠ patternId := by
    intro same
    have bodyAtPattern : SourcePreparedSharedRows.read heap patternId = some body := by
      rw [← same]
      exact bodyRead
    have equal : body = pattern := Option.some.inj (bodyAtPattern.symm.trans patternRead)
    have bodyClosed : body.free = [] := (congrArg Value.free equal).trans _patternClosed
    rw [bodyShape] at bodyClosed
    change [Reference.interned entry.identity] = [] at bodyClosed
    cases bodyClosed
  have originalValid : Cache.Valid original.2 :=
    (IntersectionEmptyDomain.make_correct domains cacheValid _).1
  have originalKey : original.1.key = extend IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.bindings universeValue pattern).map Prod.fst)
      (pair entry.identity patternId) :=
    SourceRecursiveIntersectionSchedule.entered_key domains cacheValid IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
  have diagonalKey : diagonalFirst.1.key = extend original.1.key
      ((SourceRecursiveIntersectionEnvironment.bindings universeValue referenceValue).map Prod.fst)
      (pair entry.identity entry.identity) :=
    SourceRecursiveIntersectionSchedule.entered_key original.2 originalValid original.1.key
      universeValue referenceValue entry.identity entry.identity
  have fresh : pair bodyEntry.identity entry.identity ∉ diagonalFirst.1.key.seen := by
    intro member
    rw [diagonalKey] at member
    rcases (extend_seen _ _ _ _).mp member with same | previous
    · have lower := congrArg Prod.fst same
      have upper := congrArg Prod.snd same
      simp only [pair, Nat.min_self, Nat.max_self] at lower upper
      exact bodyApart (by omega)
    · rw [originalKey] at previous
      rcases (extend_seen _ _ _ _).mp previous with same | empty
      · have lower := congrArg Prod.fst same
        have upper := congrArg Prod.snd same
        simp only [pair] at lower upper
        exact bodyPatternApart (by omega)
      · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at empty
  have tagOrder : compare (1 : Nat) 4 = .lt := by decide
  have selected : decision diagonalFirst.1.key body referenceValue = .rightReference := by
    rw [bodyShape]
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      referenceValue, Value.referenceOf, Value.free, fresh, tagOrder]
  have compiled : compileNode ⟨diagonalFirst.1, body, referenceValue⟩ =
      compileReference diagonalFirst.1 entry.identity body false :=
    reference_code diagonalFirst.1 entry.identity body selected
  have bound : entry.identity ∈ names diagonalFirst.1.key := by
    rw [diagonalKey, extend_names]
    left
    simp [SourceRecursiveIntersectionEnvironment.bindings, SourceRecursiveIntersectionEnvironment.binder,
      universeValue, referenceValue]
  refine ⟨bodyEntry, bodyRows, bodyShape, bound, fresh, selected, compiled, ?_⟩
  intro current currentFacts currentGrowth
  have currentUniverse : Available current.native.machine.heap universeValue :=
    currentFacts.cached.nodes key _ (currentGrowth.nodeRecords key _ stored)
  have read : SourcePreparedSharedRows.read current.native.machine.heap entry.identity = some universeValue :=
    SourcePreparedSharedRows.read_identity current.native.machine.heap currentFacts
      universeValue currentUniverse entry.identity rfl
  refine ⟨read, ?_⟩
  exact (congrArg (fun code : Code Symbol Guard (Value Symbol Guard) =>
      SourceEqualityNativeDemand.step (.code code) current) compiled).trans
    (reference_read_step diagonalFirst.1 entry.identity body universeValue current bound read)

end MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalFirstBodyReferenceRead
