-- UNCOMPILED CANDIDATE. This file is outside the live module tree.
-- This selected step does not prove the full simultaneous atom theorem.
import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms
import MicroCFTA.SourceRecursiveIntersectionKernelVerified

namespace MicroCFTA.SourceSynthesisCurrentUniverseMuAtomInductionStep
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedBoundaryAtoms
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- The selected original Mu step uses its exact smaller-fuel mixed body call. -/
theorem current_stored_universe_selected_mu_atoms_of_mixed_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
    (patternClosed : pattern.free = [])
    (patternAtoms : ∀ atom ∈ atoms pattern, atom = .mu entry.identity)
    (patternId : Nat) (patternIdentity : identity pattern = some patternId)
    (patternShape : tag pattern = 1 ∨ tag pattern = 3)
    (fuel : Nat) (leftIsU : Bool)
    (selected :
      decision IntersectionEmptyDomain.emptyDomain.key
        (if leftIsU then .mu entry body depth ordinary else pattern)
        (if leftIsU then pattern else .mu entry body depth ordinary) =
      (if leftIsU then .leftMu else .rightMu))
    (mixedInduction :
      let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        (.mu entry body depth ordinary) pattern entry.identity patternId
      let current : Machine Symbol Guard := ⟨heap, entered.2⟩
      Checked current
        (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1
          (if leftIsU then body else pattern) (if leftIsU then pattern else body) current)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ atoms value, atom = .mu entry.identity)) :
    let initial : Machine Symbol Guard := ⟨heap, domains⟩
    Checked initial
      (execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1) IntersectionEmptyDomain.emptyDomain
        (if leftIsU then .mu entry body depth ordinary else pattern)
        (if leftIsU then pattern else .mu entry body depth ordinary) initial)
      (fun after value => Available after.heap value ∧ value.free = [] ∧
        ∀ atom ∈ atoms value, atom = .mu entry.identity) := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, domains⟩
  let current : Machine Symbol Guard := ⟨heap, entered.2⟩
  let property : Machine Symbol Guard → Value Symbol Guard → Prop := fun after value =>
    Available after.heap value ∧ value.free = [] ∧ ∀ atom ∈ atoms value, atom = .mu entry.identity
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have patternBody : SourceRecursiveIntersectionKernel.body pattern = pattern := by
    cases pattern <;> try rfl
    simp [tag] at patternShape
  have patternBinder : SourceRecursiveIntersectionEnvironment.binder pattern = [] := by
    cases pattern <;> try rfl
    simp [tag] at patternShape
  have pairReverse : pair patternId entry.identity = pair entry.identity patternId := by
    simp only [pair, Nat.min_comm, Nat.max_comm]
  have enterReverse :
      SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        pattern universeValue patternId entry.identity = entered := by
    simp only [SourceRecursiveIntersectionEnvironment.enter, SourceRecursiveIntersectionEnvironment.bindings,
      patternBinder, SourceRecursiveIntersectionEnvironment.binder, universeValue,
      List.nil_append, List.append_nil, pairReverse, entered]
  have allocation := SourceRecursiveIntersectionKernel.entered initial ⟨facts, cacheValid⟩
    IntersectionEmptyDomain.emptyDomain (empty_domain initial)
    universeValue pattern universeAvailable patternAvailable entry.identity patternId
  have allocationExtension : Extension initial current := allocation.2.1
  have selectedEquation :
      execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1) IntersectionEmptyDomain.emptyDomain
        (if leftIsU then universeValue else pattern) (if leftIsU then pattern else universeValue) initial =
      (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1
        (if leftIsU then body else pattern) (if leftIsU then pattern else body) current).bind
        (fun value after => construction
          (SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity patternId) value after.heap) after) := by
    cases leftIsU with
    | false =>
        have branch : decision IntersectionEmptyDomain.emptyDomain.key pattern universeValue = .rightMu := selected
        change execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1)
          IntersectionEmptyDomain.emptyDomain pattern universeValue initial =
          (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 pattern body current).bind
            (fun value after => construction
              (SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity patternId) value after.heap) after)
        rw [execute]
        simp only [onNode, branch, mu, patternIdentity,
          show identity universeValue = some entry.identity from rfl]
        rw [enterReverse]
        simp only [patternBody, SourceRecursiveIntersectionKernel.body, universeValue,
          pairReverse, initial, current, entered]
    | true =>
        have branch : decision IntersectionEmptyDomain.emptyDomain.key universeValue pattern = .leftMu := selected
        change execute top SourceEqualityPCSNativeEdge.conjoin (fuel + 1)
          IntersectionEmptyDomain.emptyDomain universeValue pattern initial =
          (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 body pattern current).bind
            (fun value after => construction
              (SourceRecursiveIntersectionMaybeMu.maybeMu (pair entry.identity patternId) value after.heap) after)
        rw [execute]
        simp only [onNode, branch, mu, patternIdentity,
          show identity universeValue = some entry.identity from rfl]
        simp only [patternBody, SourceRecursiveIntersectionKernel.body, universeValue,
          initial, current, entered]
  change Checked initial _ property
  rw [selectedEquation]
  apply Checked.prepend allocationExtension
  apply checked_bind current _ _ property property mixedInduction
  intro value after _returned afterValid good
  have unused := SourceRecursiveIntersectionMaybeMu.unused
    (pair entry.identity patternId) value after.heap (by simp [good.2.1])
  rw [unused]
  change Checked after (.done value after) property
  exact checked_pure after afterValid value property good

end MicroCFTA.SourceSynthesisCurrentUniverseMuAtomInductionStep
