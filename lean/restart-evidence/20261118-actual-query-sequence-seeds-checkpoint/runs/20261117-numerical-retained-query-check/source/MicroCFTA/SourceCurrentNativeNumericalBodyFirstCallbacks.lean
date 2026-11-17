import MicroCFTA.SourceCurrentNativeWarmBodyFirstInitialPayloads

namespace MicroCFTA.SourceCurrentNativeNumericalBodyFirstCallbacks
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Numerical source body-first callbacks]
The original stored source fixes the body and universe records.
The numerical key binds the source universe and two explicit identities.
Both identity exclusions are past numerical conditions.
The callbacks quantify over every equal-key domain and grown physical heap.
No future source entry or returned payload law is an input.
-/

theorem original_universe_body_first_callbacks_at_numerical_base
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (heap : InternedConstructorTemplates.State Symbol Guard) (facts : Facts heap)
    (sourceGrowth : Grows sourceHeap heap)
    (patternId : Nat) (patternUniverseApart : patternId ≠ entry.identity)
    (patternBodyApart : patternId ≠ bodyId) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
    let baseKey := extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId)
    let selectedKey := extend baseKey [entry.identity] (pair bodyId entry.identity)
    (∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (InternedEdgeResidency.nodeEdges body) (InternedEdgeResidency.nodeEdges body)) ∧
    (∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      decision actualDomain.key universeValue referenceValue = .leftMu) ∧
    (∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current actualDomain.key
        universeValue referenceValue entry.identity entry.identity).1,
        SourceRecursiveIntersectionKernel.body universeValue,
        SourceRecursiveIntersectionKernel.body referenceValue⟩ =
        .pure (repeatedValue (pair bodyId entry.identity))) ∧
    (let binder := pair entry.identity entry.identity;
      Reference.intersection binder.1 binder.2 ∉
        (repeatedValue (pair bodyId entry.identity) : Value Symbol Guard).free) ∧
    (∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      ∀ current : Checked width, Physical current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨actualDomain, referenceValue, referenceValue⟩)) current =
        .yielded (.code (requestNode actualDomain universeValue referenceValue)) current) := by
  have _retainedPatternBodyApart := patternBodyApart
  obtain ⟨bodyEntry, _marker, arrow, rows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts sourceGrowth
  have actualBodyIdentity : identity body = some bodyEntry.identity := by
    rw [bodyShape]
    rfl
  have sameBodyId : bodyId = bodyEntry.identity :=
    Option.some.inj (bodyIdentity.symm.trans actualBodyIdentity)
  subst bodyId
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let baseKey := extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId)
  let selectedKey := extend baseKey [entry.identity] (pair bodyEntry.identity entry.identity)
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (sourceGrowth.nodeRecords key _ stored)
  have bodyApart : bodyEntry.identity ≠ entry.identity := by
    apply SourceSynthesisUniverseBodyReferenceControl.body_identity_ne
      entry bodyEntry (canonicalEdges (arrow :: rows)) depth ordinary ⟨heap, Cache.emptyState⟩ facts
    change Available heap (.mu entry
      (.node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity]) depth ordinary)
    rw [← bodyShape]
    exact universeAvailable
  have diagonalParts (first second owner : Nat) (same : pair first second = pair owner owner) :
      first = owner ∧ second = owner := by
    have lower := congrArg Prod.fst same
    have upper := congrArg Prod.snd same
    simp only [pair, Nat.min_self, Nat.max_self] at lower upper
    omega
  have freshBody : pair bodyEntry.identity bodyEntry.identity ∉ selectedKey.seen := by
    intro member
    rcases (extend_seen _ _ _ _).mp member with same | previous
    · exact bodyApart
        (diagonalParts bodyEntry.identity entry.identity bodyEntry.identity same.symm).2.symm
    · rcases (extend_seen _ _ _ _).mp previous with same | empty
      · exact bodyApart
          (diagonalParts entry.identity patternId bodyEntry.identity same.symm).1.symm
      · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at empty
  have freshDiagonal : pair entry.identity entry.identity ∉ selectedKey.seen := by
    intro member
    rcases (extend_seen _ _ _ _).mp member with same | previous
    · exact bodyApart
        (diagonalParts bodyEntry.identity entry.identity entry.identity same.symm).1
    · rcases (extend_seen _ _ _ _).mp previous with same | empty
      · exact patternUniverseApart
          (diagonalParts entry.identity patternId entry.identity same.symm).2
      · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at empty
  have sourceRows : InternedEdgeResidency.nodeEdges body = canonicalEdges (arrow :: rows) := by
    rw [bodyShape]
    rfl
  have compiler : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      compileNode ⟨actualDomain, body, body⟩ =
        compileRows actualDomain (InternedEdgeResidency.nodeEdges body) (InternedEdgeResidency.nodeEdges body) := by
    intro actualDomain sameKey
    have fresh : pair bodyEntry.identity bodyEntry.identity ∉ actualDomain.key.seen := by
      rw [sameKey]
      exact freshBody
    have shaped : decision actualDomain.key
        (.node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity])
        (.node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity]) = .ordinary := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
        Value.referenceOf, Value.free, fresh]
    have literalCompiled : compileNode ⟨actualDomain,
        .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity],
        .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity]⟩ =
        compileRows actualDomain (canonicalEdges (arrow :: rows)) (canonicalEdges (arrow :: rows)) := by
      simp only [compileNode, shaped]
    calc
      compileNode ⟨actualDomain, body, body⟩ = compileNode ⟨actualDomain,
          .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity],
          .node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity]⟩ :=
        congrArg (fun value : Value Symbol Guard => compileNode ⟨actualDomain, value, value⟩) bodyShape
      _ = compileRows actualDomain (canonicalEdges (arrow :: rows)) (canonicalEdges (arrow :: rows)) := literalCompiled
      _ = compileRows actualDomain (InternedEdgeResidency.nodeEdges body)
          (InternedEdgeResidency.nodeEdges body) := by rw [sourceRows]
  have selected : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey → decision actualDomain.key universeValue referenceValue = .leftMu := by
    intro actualDomain sameKey
    have fresh : pair entry.identity entry.identity ∉ actualDomain.key.seen := by
      rw [sameKey]
      exact freshDiagonal
    have tagOrder : compare (2 : Nat) 4 = .lt := by decide
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      universeValue, referenceValue, Value.referenceOf, Value.free, fresh, tagOrder]
  have childPure : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current actualDomain.key
        universeValue referenceValue entry.identity entry.identity).1,
        SourceRecursiveIntersectionKernel.body universeValue,
        SourceRecursiveIntersectionKernel.body referenceValue⟩ =
        .pure (repeatedValue (pair bodyEntry.identity entry.identity)) := by
    intro actualDomain sameKey current currentValid
    let entered := SourceRecursiveIntersectionEnvironment.enter current actualDomain.key
      universeValue referenceValue entry.identity entry.identity
    have enteredKey := SourceRecursiveIntersectionSchedule.entered_key current currentValid actualDomain.key
      universeValue referenceValue entry.identity entry.identity
    change entered.1.key = extend actualDomain.key [entry.identity]
      (pair entry.identity entry.identity) at enteredKey
    have extra : pair bodyEntry.identity entry.identity ∈ entered.1.key.seen := by
      rw [enteredKey, sameKey]
      apply (extend_seen _ _ _ _).mpr
      right
      exact (extend_seen _ _ _ _).mpr (Or.inl rfl)
    change compileNode ⟨entered.1, body, referenceValue⟩ = _
    have tagOrder : compare (1 : Nat) 4 = .lt := by decide
    have shaped : decision entered.1.key
        (.node bodyEntry (canonicalEdges (arrow :: rows)) 0 [.interned entry.identity]) referenceValue =
        .repeated (pair bodyEntry.identity entry.identity) := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity,
        referenceValue, Value.referenceOf, Value.free, extra, tagOrder]
    have chosen : decision entered.1.key body referenceValue =
        .repeated (pair bodyEntry.identity entry.identity) := by
      rw [bodyShape]
      exact shaped
    simp only [compileNode, chosen]
  have absent : let binder := pair entry.identity entry.identity
      Reference.intersection binder.1 binder.2 ∉
        (repeatedValue (pair bodyEntry.identity entry.identity) : Value Symbol Guard).free := by
    dsimp only [repeatedValue, Value.free]
    intro member
    have components := Reference.intersection.inj (List.mem_singleton.mp member)
    have samePair : pair bodyEntry.identity entry.identity = pair entry.identity entry.identity :=
      Prod.ext components.1.symm components.2.symm
    exact bodyApart (diagonalParts bodyEntry.identity entry.identity entry.identity samePair).1
  have read : ∀ actualDomain : Interned IntersectionFlatMemoKeyDomain.DomainKey,
      actualDomain.key = selectedKey →
      ∀ current : Checked width, Physical current.native →
      Grows sourceHeap current.native.machine.heap →
      SourceEqualityNativeDemand.step
        (.code (compileNode ⟨actualDomain, referenceValue, referenceValue⟩)) current =
        .yielded (.code (requestNode actualDomain universeValue referenceValue)) current := by
    intro actualDomain sameKey current physical currentGrowth
    have bound : entry.identity ∈ names actualDomain.key := by
      rw [sameKey]
      exact (extend_names _ _ _ _).mpr (Or.inl (List.mem_singleton.mpr rfl))
    have fresh : pair entry.identity entry.identity ∉ actualDomain.key.seen := by
      rw [sameKey]
      exact freshDiagonal
    have referenceSelected : decision actualDomain.key referenceValue referenceValue = .leftReference := by
      simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
        referenceValue, Value.referenceOf, Value.free, fresh,
        SourceRecursiveIntersectionSchedule.reference_interned]
    have compiled : compileNode ⟨actualDomain, referenceValue, referenceValue⟩ =
        compileReference actualDomain entry.identity referenceValue true := by
      simp only [compileNode, referenceSelected, referenceValue]
    have currentUniverse : Available current.native.machine.heap universeValue :=
      physical.machine.1.cached.nodes key _ (currentGrowth.nodeRecords key _ stored)
    have sourceRead : SourcePreparedSharedRows.read current.native.machine.heap entry.identity =
        some universeValue := SourcePreparedSharedRows.read_identity current.native.machine.heap
      physical.machine.1 universeValue currentUniverse entry.identity rfl
    have readStep : SourceEqualityNativeDemand.step
        (.code (compileReference actualDomain entry.identity referenceValue true)) current =
        .yielded (.code (requestNode actualDomain universeValue referenceValue)) current := by
      simp [compileReference, bound, SourceEqualityNativeDemand.step,
        SourceRecursiveIntersectionNative.step, sourceRead, SourceEqualityNativeDemand.lift]
    exact (congrArg (fun code : Code Symbol Guard (Value Symbol Guard) =>
      SourceEqualityNativeDemand.step (.code code) current) compiled).trans readStep
  exact ⟨compiler, selected, childPure, absent, read⟩

end MicroCFTA.SourceCurrentNativeNumericalBodyFirstCallbacks

#print axioms MicroCFTA.SourceCurrentNativeNumericalBodyFirstCallbacks.original_universe_body_first_callbacks_at_numerical_base
