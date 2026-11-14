import MicroCFTA.SourceSynthesisCurrentUniverseEmptyDomainInduction
import MicroCFTA.SourceSynthesisCurrentUniverseMixedInductionAssembly

namespace MicroCFTA.SourceSynthesisCurrentUniverseGeneratedTypeClosure
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (NodeKey Reference)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceRecursiveIntersectionKernel
open SourceSynthesisUniversePrefixHeight (height)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- Strong fuel induction combines the exact original closed and mixed source cases. -/
theorem current_stored_universe_coupled_fuel_atoms
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (fuel : Nat) :
    (∀ (heap : State Symbol Guard) (_facts : Facts heap) (_growth : Grows sourceHeap heap)
      (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (_cacheValid : Cache.Valid domains)
      (left right : Value Symbol Guard),
      Available heap left → Available heap right → left.free = [] → right.free = [] →
      (∀ atom ∈ InternedBoundaryAtoms.atoms left, atom = .mu entry.identity) →
      (∀ atom ∈ InternedBoundaryAtoms.atoms right, atom = .mu entry.identity) →
      let initial : Machine Symbol Guard := ⟨heap, domains⟩
      Checked initial
        (execute top SourceEqualityPCSNativeEdge.conjoin fuel IntersectionEmptyDomain.emptyDomain left right initial)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity)) ∧
    (∀ (heap : State Symbol Guard) (_facts : Facts heap) (_growth : Grows sourceHeap heap)
      (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (_cacheValid : Cache.Valid domains)
      (pattern : Value Symbol Guard) (patternId : Nat),
      Available heap pattern → pattern.free = [] →
      SourceRecursiveIntersectionControl.identity pattern = some patternId →
      (SourceRecursiveIntersectionControl.tag pattern = 1 ∨ SourceRecursiveIntersectionControl.tag pattern = 3) →
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
      ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
      ∀ openAlias : Value Symbol Guard, (openAlias = body ∨ openAlias = .reference (.interned entry.identity)) →
      ∀ operand : Value Symbol Guard, Available later.heap operand → operand.free = [] →
      (∀ atom ∈ InternedBoundaryAtoms.atoms operand, atom = .mu entry.identity) →
      height operand ≤ height pattern →
      (openAlias = .reference (.interned entry.identity) → height operand < height pattern) →
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 openAlias operand later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) ∧
      Checked later (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 operand openAlias later)
        (fun after value => Available after.heap value ∧ value.free = [] ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity)) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel smallerResults =>
      exact ⟨SourceSynthesisCurrentUniverseEmptyDomainInduction.current_stored_universe_empty_domain_of_coupled_fuel_induction
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored fuel smallerResults,
        SourceSynthesisCurrentUniverseMixedInductionAssembly.current_stored_universe_mixed_of_coupled_strong_induction
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored fuel smallerResults⟩

/-- The original closed atom claim follows from the checked closed conjunct. -/
theorem current_stored_universe_closed_type_intersection_atoms
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
    (left right : Value Symbol Guard)
    (leftAvailable : Available heap left) (rightAvailable : Available heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftAtoms : ∀ atom ∈ InternedBoundaryAtoms.atoms left, atom = .mu entry.identity)
    (rightAtoms : ∀ atom ∈ InternedBoundaryAtoms.atoms right, atom = .mu entry.identity)
    (fuel : Nat) :
    let initial : Machine Symbol Guard := ⟨heap, domains⟩
    Checked initial
      (execute top SourceEqualityPCSNativeEdge.conjoin fuel IntersectionEmptyDomain.emptyDomain
        left right initial)
      (fun _ value => ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) := by
  have checked := (current_stored_universe_coupled_fuel_atoms
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored fuel).1
    heap facts growth domains cacheValid left right leftAvailable rightAvailable
    leftClosed rightClosed leftAtoms rightAtoms
  refine ⟨checked.valid, checked.extension, ?_⟩
  intro value after returned
  exact (checked.result value after returned).2.2

end MicroCFTA.SourceSynthesisCurrentUniverseGeneratedTypeClosure
