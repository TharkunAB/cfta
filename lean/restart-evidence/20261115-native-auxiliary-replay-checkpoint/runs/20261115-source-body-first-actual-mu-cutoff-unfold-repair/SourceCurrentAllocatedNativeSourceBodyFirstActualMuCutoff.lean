import MicroCFTA.SourceCurrentAllocatedNativeAuxiliaryCutoffQueries
import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness
import MicroCFTA.SourceSynthesisUniverseBodyReferenceControl
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence
import MicroCFTA.SourceRecursiveIntersectionMaybeMu

/-!
# Body-first Mu cutoff at the actual current domain cache

The original source determines the body-first parent selection.
Actual current entry preserves the canonical child key.
The unused diagonal binder returns the same open body cutoff.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff
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

set_option maxHeartbeats 1200000 in
/-- The actual body-first Mu entry selects its source cutoff in every valid current domain cache. -/
theorem current_stored_universe_body_first_actual_mu_cutoff
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
      let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        body universeValue bodyEntry.identity entry.identity
      let bodyTerminal := SourceRecursiveIntersectionEnvironment.enter bodyFirst.2 bodyFirst.1.key
        universeValue referenceValue entry.identity entry.identity
      let binder := pair entry.identity entry.identity
      let cutoff := repeatedValue (pair bodyEntry.identity entry.identity)
      decision bodyFirst.1.key universeValue referenceValue = .leftMu ∧
      compileNode ⟨bodyFirst.1, universeValue, referenceValue⟩ =
        compileMu bodyFirst.1 universeValue referenceValue ∧
      Reference.intersection binder.1 binder.2 ∉ cutoff.free ∧
      (∀ (current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey), Cache.Valid current →
        let actualEntered := SourceRecursiveIntersectionEnvironment.enter current bodyFirst.1.key
          universeValue referenceValue entry.identity entry.identity
        actualEntered.1.key = bodyTerminal.1.key ∧
        decision actualEntered.1.key body referenceValue = .repeated (pair bodyEntry.identity entry.identity) ∧
        compileNode ⟨actualEntered.1, body, referenceValue⟩ = .pure cutoff) ∧
      (∀ currentHeap : InternedConstructorTemplates.State Symbol Guard,
        SourceRecursiveIntersectionMaybeMu.maybeMu binder cutoff currentHeap = .done cutoff currentHeap) := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, sourceQueries⟩ :=
    SourceCurrentAllocatedNativeAuxiliaryCutoffQueries.current_stored_universe_auxiliary_cutoff_queries
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern _patternAvailable _patternClosed patternId
      _patternIdentity _patternKind
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    body universeValue bodyEntry.identity entry.identity
  let bodyTerminal := SourceRecursiveIntersectionEnvironment.enter bodyFirst.2 bodyFirst.1.key
    universeValue referenceValue entry.identity entry.identity
  let binder : Nat × Nat := pair entry.identity entry.identity
  let cutoff : Value Symbol Guard := repeatedValue (pair bodyEntry.identity entry.identity)
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have universeClosed : universeValue.free = [] :=
    SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth universeValue universeAvailable (by
        intro atom member
        simpa only [universeValue, InternedBoundaryAtoms.atoms, List.mem_singleton] using member)
  have bodyApart : bodyEntry.identity ≠ entry.identity := by
    apply SourceSynthesisUniverseBodyReferenceControl.body_identity_ne
      entry bodyEntry bodyRows depth ordinary ⟨heap, domains⟩ facts
    change Available heap (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary)
    rw [← bodyShape]
    exact universeAvailable
  have patternApart : patternId ≠ entry.identity := by
    intro same
    have identified : identity pattern = some entry.identity := by
      rw [← same]
      exact _patternIdentity
    have sameValue := SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective
      heap facts pattern universeValue _patternAvailable universeAvailable _patternClosed universeClosed
      entry.identity identified rfl
    rcases _patternKind with nodeKind | unionKind
    · rw [sameValue] at nodeKind
      change (2 : Nat) = 1 at nodeKind
      cases nodeKind
    · rw [sameValue] at unionKind
      change (2 : Nat) = 3 at unionKind
      cases unionKind
  have originalValid : Cache.Valid original.2 :=
    (IntersectionEmptyDomain.make_correct domains cacheValid _).1
  have bodyValid : Cache.Valid bodyFirst.2 :=
    (IntersectionEmptyDomain.make_correct original.2 originalValid _).1
  have originalKey : original.1.key = extend IntersectionEmptyDomain.emptyKey
      ((SourceRecursiveIntersectionEnvironment.bindings universeValue pattern).map Prod.fst)
      (pair entry.identity patternId) :=
    SourceRecursiveIntersectionSchedule.entered_key domains cacheValid IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
  have bodyKey : bodyFirst.1.key = extend original.1.key
      ((SourceRecursiveIntersectionEnvironment.bindings body universeValue).map Prod.fst)
      (pair bodyEntry.identity entry.identity) :=
    SourceRecursiveIntersectionSchedule.entered_key original.2 originalValid original.1.key
      body universeValue bodyEntry.identity entry.identity
  have diagonalParts (first second owner : Nat) (same : pair first second = pair owner owner) :
      first = owner ∧ second = owner := by
    have lower := congrArg Prod.fst same
    have upper := congrArg Prod.snd same
    simp only [pair, Nat.min_self, Nat.max_self] at lower upper
    omega
  have diagonalFresh : pair entry.identity entry.identity ∉ bodyFirst.1.key.seen := by
    intro member
    rw [bodyKey] at member
    rcases (extend_seen _ _ _ _).mp member with same | previous
    · exact bodyApart (diagonalParts bodyEntry.identity entry.identity entry.identity same.symm).1
    · rw [originalKey] at previous
      rcases (extend_seen _ _ _ _).mp previous with same | empty
      · exact patternApart (diagonalParts entry.identity patternId entry.identity same.symm).2
      · simp only [IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at empty
  have tagOrder : compare (2 : Nat) 4 = .lt := by decide
  have selected : decision bodyFirst.1.key universeValue referenceValue = .leftMu := by
    simp [decision, hasEmpty, reset, closedSelf, greater, compareValue, tag, identity, payload,
      universeValue, referenceValue, Value.referenceOf, Value.free, diagonalFresh, tagOrder]
  have compiled : compileNode ⟨bodyFirst.1, universeValue, referenceValue⟩ =
      compileMu bodyFirst.1 universeValue referenceValue := by
    simp only [compileNode, selected]
  have absent : Reference.intersection binder.1 binder.2 ∉ cutoff.free := by
    intro member
    have same := List.mem_singleton.mp member
    have components := Reference.intersection.inj same
    have samePair : pair bodyEntry.identity entry.identity = pair entry.identity entry.identity :=
      Prod.ext components.1.symm components.2.symm
    exact bodyApart (diagonalParts bodyEntry.identity entry.identity entry.identity samePair).1
  refine ⟨bodyEntry, bodyRows, bodyShape, bodyApart, selected, compiled, absent, ?_, ?_⟩
  · intro current currentValid
    let actualEntered := SourceRecursiveIntersectionEnvironment.enter current bodyFirst.1.key
      universeValue referenceValue entry.identity entry.identity
    have keysSame : actualEntered.1.key = bodyTerminal.1.key :=
      (SourceRecursiveIntersectionSchedule.entered_key current currentValid bodyFirst.1.key
        universeValue referenceValue entry.identity entry.identity).trans
        (SourceRecursiveIntersectionSchedule.entered_key bodyFirst.2 bodyValid bodyFirst.1.key
          universeValue referenceValue entry.identity entry.identity).symm
    dsimp only at sourceQueries
    have historical : decision bodyTerminal.1.key body referenceValue =
        .repeated (pair bodyEntry.identity entry.identity) :=
      (sourceQueries ⟨bodyTerminal.1, body, referenceValue⟩ (pair bodyEntry.identity entry.identity)
        (Or.inl ⟨rfl, rfl⟩)).1
    have currentSelected : decision actualEntered.1.key body referenceValue =
        .repeated (pair bodyEntry.identity entry.identity) := by
      rw [keysSame]
      exact historical
    refine ⟨keysSame, currentSelected, ?_⟩
    unfold compileNode
    rw [currentSelected]
  · intro currentHeap
    exact SourceRecursiveIntersectionMaybeMu.unused binder cutoff currentHeap absent

end MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff
