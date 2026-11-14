-- UNCOMPILED SOURCE DRAFT. Root owns validation.
import MicroCFTA.SourceSynthesisCurrentUniverseReferenceIdentity
import MicroCFTA.SourceRecursiveIntersectionKernelVerified
import MicroCFTA.InternedBoundaryAtoms

/-!
# Checked boundary atoms for actual mixed-domain aliases

The same accepted source build supplies both aliases and the original Mu.
Each successful native fuel has that exact value. Failed native calls retain
validity and cache growth. This result does not describe stopped worker histories.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseAliasAtoms
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedRecordCoherence
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- Every native fuel preserves atoms for either original alias in the actual mixed domain. -/
theorem current_stored_universe_open_alias_checked_after_mixed_entry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (patternAvailable : Available heap pattern) (patternClosed : pattern.free = [])
    (patternIdentity : SourceRecursiveIntersectionControl.identity pattern = some patternId)
    (patternShape : SourceRecursiveIntersectionControl.tag pattern = 1 ∨
      SourceRecursiveIntersectionControl.tag pattern = 3)
    (left : Value Symbol Guard)
    (leftAlias : left = .reference (.interned entry.identity) ∨ left = body)
    (fuel : Nat) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    Checked initial
      (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 left universeValue initial)
      (fun after value => Available after.heap value ∧ value = universeValue ∧
        ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  have universeAvailable : Available heap universeValue :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have mixedChecked := SourceRecursiveIntersectionKernel.entered
    (⟨heap, domains⟩ : Machine Symbol Guard) ⟨facts, cacheValid⟩
    IntersectionEmptyDomain.emptyDomain (empty_domain _) universeValue pattern universeAvailable patternAvailable
    entry.identity patternId
  have leftAvailable : Available heap left := by
    rcases leftAlias with leftRef | leftBody
    · rw [leftRef]
      have installed := InternedFreshProbeKeys.resident_entry heap facts.coherent universeValue universeAvailable.resident entry rfl
      have issued := (facts.coherent.valid.2.2 entry.key entry installed).2
      apply reference_available
      intro identity member
      have same : identity = entry.identity := by simpa [Value.free] using member
      subst identity
      exact ⟨entry.key, issued⟩
    · rw [leftBody]
      exact body_available heap universeValue universeAvailable
  have native := execute_checked top SourceEqualityPCSNativeEdge.conjoin fuel
    entered.1 left universeValue initial mixedChecked.1 mixedChecked.2.2 leftAvailable universeAvailable
  obtain ⟨_bound, _final, _stable, _valid, _extension, successful⟩ :=
    SourceSynthesisCurrentUniverseReferenceIdentity.current_stored_universe_open_alias_at_every_successful_fuel
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth domains cacheValid pattern patternId patternAvailable patternClosed patternIdentity patternShape
      left leftAlias
  refine ⟨native.valid, native.extension, ?_⟩
  intro value after observed
  have same := (successful fuel value after observed).1
  refine ⟨native.result value after observed, same, ?_⟩
  rw [same]
  intro atom member
  simpa only [universeValue, InternedBoundaryAtoms.atoms, List.mem_singleton] using member

end MicroCFTA.SourceSynthesisCurrentUniverseAliasAtoms

#print axioms MicroCFTA.SourceSynthesisCurrentUniverseAliasAtoms.current_stored_universe_open_alias_checked_after_mixed_entry
