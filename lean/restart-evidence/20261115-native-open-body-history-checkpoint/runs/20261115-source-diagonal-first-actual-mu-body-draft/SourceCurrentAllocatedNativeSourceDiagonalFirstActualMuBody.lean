import MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalFirstBodyReferenceRead

/-!
# Actual current-cache Mu and ordinary-body source selection

Original source records distinguish the body identity from U.
The diagonal-first B/U call selects the actual right-Mu branch.
Current cache entry retains the terminal structural key.
Every actual handle with that key selects the open B/B row product.
No structural key equation identifies independently allocated handles.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The original source selects the current-cache right-Mu call and open ordinary body product. -/
theorem current_stored_universe_diagonal_first_actual_mu_body
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
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧ bodyEntry.identity ≠ entry.identity ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        universeValue referenceValue entry.identity entry.identity
      let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
        body universeValue bodyEntry.identity entry.identity
      identity body = some bodyEntry.identity ∧ identity universeValue = some entry.identity ∧
      body.free ≠ [] ∧ pair entry.identity entry.identity ≠ pair bodyEntry.identity entry.identity ∧
      (∀ (actualIncoming : Interned IntersectionFlatMemoKeyDomain.DomainKey),
        actualIncoming.key = diagonalFirst.1.key →
        decision actualIncoming.key body universeValue = .rightMu ∧
        compileNode ⟨actualIncoming, body, universeValue⟩ = compileMu actualIncoming body universeValue ∧
        ∀ (current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey), Cache.Valid current →
          (SourceRecursiveIntersectionEnvironment.enter current actualIncoming.key
            body universeValue bodyEntry.identity entry.identity).1.key = diagonalTerminal.1.key) ∧
      (∀ (actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
        actualDomain.key = diagonalTerminal.1.key →
        pair bodyEntry.identity bodyEntry.identity ∉ actualDomain.key.seen ∧
        decision actualDomain.key body body = .ordinary ∧
        compileNode ⟨actualDomain, body, body⟩ =
          compileRows actualDomain (nodeEdges body) (nodeEdges body)) := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, sourceRead⟩ :=
    SourceCurrentAllocatedNativeSourceDiagonalFirstBodyReferenceRead.current_stored_universe_diagonal_first_body_reference_read
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern _patternAvailable _patternClosed patternId
      _patternIdentity _patternKind
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let diagonalFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    universeValue referenceValue entry.identity entry.identity
  let diagonalTerminal := SourceRecursiveIntersectionEnvironment.enter diagonalFirst.2 diagonalFirst.1.key
    body universeValue bodyEntry.identity entry.identity
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have bodyApart : bodyEntry.identity ≠ entry.identity := by
    apply SourceSynthesisUniverseBodyReferenceControl.body_identity_ne
      entry bodyEntry bodyRows depth ordinary ⟨heap, domains⟩ facts
    change Available heap (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary)
    rw [← bodyShape]
    exact universeAvailable
  have bodyIdentity : identity body = some bodyEntry.identity := by
    rw [bodyShape]
    rfl
  have bodyOpen : body.free ≠ [] := by
    rw [bodyShape]
    change [Reference.interned entry.identity] ≠ []
    intro impossible
    cases impossible
  have sourceRows : nodeEdges body = bodyRows := by
    rw [bodyShape]
    rfl
  have originalValid : Cache.Valid original.2 :=
    (IntersectionEmptyDomain.make_correct domains cacheValid _).1
  have diagonalValid : Cache.Valid diagonalFirst.2 :=
    (IntersectionEmptyDomain.make_correct original.2 originalValid _).1
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
  have terminalKey : diagonalTerminal.1.key = extend diagonalFirst.1.key
      ((SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst)
      (pair bodyEntry.identity entry.identity) :=
    SourceRecursiveIntersectionSchedule.entered_key diagonalFirst.2 diagonalValid diagonalFirst.1.key
      body universeValue bodyEntry.identity entry.identity
  have diagonalParts (first second owner : Nat) (same : pair first second = pair owner owner) :
      first = owner ∧ second = owner := by
    have lower := congrArg Prod.fst same
    have upper := congrArg Prod.snd same
    simp only [pair, Nat.min_self, Nat.max_self] at lower upper
    omega
  have cutoffApart : pair entry.identity entry.identity ≠ pair bodyEntry.identity entry.identity := by
    intro same
    exact bodyApart (diagonalParts bodyEntry.identity entry.identity entry.identity same.symm).1
  have muFresh : pair bodyEntry.identity entry.identity ∉ diagonalFirst.1.key.seen := sourceRead.2.1
  have diagonalFresh : pair bodyEntry.identity bodyEntry.identity ∉ diagonalTerminal.1.key.seen := by
    intro member
    rw [terminalKey] at member
    rcases (extend_seen _ _ _ _).mp member with same | previous
    · exact bodyApart (diagonalParts bodyEntry.identity entry.identity bodyEntry.identity same.symm).2.symm
    · rw [diagonalKey] at previous
      rcases (extend_seen _ _ _ _).mp previous with same | earlier
      · exact bodyApart (diagonalParts entry.identity entry.identity bodyEntry.identity same.symm).1.symm
      · rw [originalKey] at earlier
        rcases (extend_seen _ _ _ _).mp earlier with same | empty
        · exact bodyApart (diagonalParts entry.identity patternId bodyEntry.identity same.symm).1.symm
        · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at empty
  refine ⟨bodyEntry, bodyRows, bodyShape, bodyApart, bodyIdentity, rfl, bodyOpen, cutoffApart, ?_, ?_⟩
  · intro actualIncoming sameKey
    have fresh : pair bodyEntry.identity entry.identity ∉ actualIncoming.key.seen := by
      rw [sameKey]
      exact muFresh
    have tagOrder : compare (1 : Nat) 2 = .lt := by decide
    have shaped : decision actualIncoming.key
        (.node bodyEntry bodyRows 0 [.interned entry.identity]) universeValue = .rightMu := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
        universeValue, Value.referenceOf, Value.free, fresh, tagOrder]
    have selected : decision actualIncoming.key body universeValue = .rightMu :=
      (congrArg (fun value : Value Symbol Guard => decision actualIncoming.key value universeValue)
        bodyShape).trans shaped
    refine ⟨selected, ?_, ?_⟩
    · simp only [compileNode, selected]
    · intro current currentValid
      rw [SourceRecursiveIntersectionSchedule.entered_key current currentValid actualIncoming.key
        body universeValue bodyEntry.identity entry.identity, sameKey]
      exact terminalKey.symm
  · intro actualDomain sameKey
    have fresh : pair bodyEntry.identity bodyEntry.identity ∉ actualDomain.key.seen := by
      rw [sameKey]
      exact diagonalFresh
    have shaped : decision actualDomain.key
        (.node bodyEntry bodyRows 0 [.interned entry.identity])
        (.node bodyEntry bodyRows 0 [.interned entry.identity]) = .ordinary := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
        Value.referenceOf, Value.free, fresh]
    have selected : decision actualDomain.key body body = .ordinary :=
      (congrArg (fun value : Value Symbol Guard => decision actualDomain.key value value) bodyShape).trans shaped
    have literalCompiled : compileNode ⟨actualDomain,
        .node bodyEntry bodyRows 0 [.interned entry.identity],
        .node bodyEntry bodyRows 0 [.interned entry.identity]⟩ = compileRows actualDomain bodyRows bodyRows := by
      simp only [compileNode, shaped]
    refine ⟨fresh, selected, ?_⟩
    calc
      compileNode ⟨actualDomain, body, body⟩ = compileNode ⟨actualDomain,
          .node bodyEntry bodyRows 0 [.interned entry.identity],
          .node bodyEntry bodyRows 0 [.interned entry.identity]⟩ :=
        congrArg (fun value : Value Symbol Guard => compileNode ⟨actualDomain, value, value⟩) bodyShape
      _ = compileRows actualDomain bodyRows bodyRows := literalCompiled
      _ = compileRows actualDomain (nodeEdges body) (nodeEdges body) := by rw [sourceRows]

end MicroCFTA.SourceCurrentAllocatedNativeSourceDiagonalFirstActualMuBody
