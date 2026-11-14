import MicroCFTA.SourceSynthesisCurrentUniverseReferenceIdentity
import MicroCFTA.SourcePruningOuterNarrow
import MicroCFTA.MergedFreshOrdinaryColdReplay
import MicroCFTA.InternedFreshOrdinarySourceFreeNames

/-!
# Exact universe identity after actual initial root narrowing

The original closed build supplies the initial ready heap.
The observed root narrowing supplies its exact reached heap.
That same heap supports the native request for the original stored Mu.
-/
namespace MicroCFTA.SourceSynthesisCurrentUniverseRootNarrowIdentity
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (NodeKey)
open InternedRecordCoherence (Covered)
open SourceRecursiveIntersectionKernel
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourcePruningRecordTypes (Metadata)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

set_option autoImplicit false

private theorem narrowAt_done_moreFuel
    {Key : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (fits : Key → Symbol → Bool) (admits : Key → Value Symbol Guard → Bool)
    (fuel extra : Nat) (key : Key) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (observed : SourcePruningNativeView.narrowAt fits admits fuel key value before = .done result after) :
    SourcePruningNativeView.narrowAt fits admits (fuel + extra) key value before = .done result after := by
  unfold SourcePruningNativeView.narrowAt at observed ⊢
  cases read : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done rows middle =>
      have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel extra value before
        (by simp only [read, MergedSourceExposure.Finished])
      rw [read] at stable
      simpa only [read, stable] using observed
  | unresolved name middle =>
      simp only [read] at observed
      cases observed
  | pending pendingKey middle =>
      simp only [read] at observed
      cases observed
  | exhausted middle =>
      simp only [read] at observed
      cases observed

private theorem narrow_done_moreFuel
    {Typing Key : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel extra uv : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (observed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value before = .done result after) :
    SourcePruningOuterNarrow.narrow holeKey fits admits metadata (fuel + extra) uv value before = .done result after := by
  by_cases typed : uv ∈ metadata.types
  · rw [SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata fuel uv value before typed] at observed
    rw [SourcePruningOuterNarrow.narrow_type holeKey fits admits metadata (fuel + extra) uv value before typed]
    exact observed
  · cases value with
    | mu entry body depth ordinary => exact observed
    | empty | reference | node | union =>
        simpa [SourcePruningOuterNarrow.narrow, typed] using
          narrowAt_done_moreFuel fits admits fuel extra (holeKey metadata.typing uv) _ before result after
            (by simpa [SourcePruningOuterNarrow.narrow, typed] using observed)

/-- The same successful root narrowing derives growth and exact original universe identity. -/
theorem current_stored_universe_reference_identity_after_root_narrowing
    {Typing Key : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol Guard → Bool) (metadata : Metadata Typing)
    (fuel : Nat) (narrowed : Value Symbol Guard) (heap : State Symbol Guard)
    (observed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata
      fuel 0 rootValue sourceHeap = .done narrowed heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (cacheValid : Cache.Valid domains) :
    (∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata
      (fuel + extra) 0 rootValue sourceHeap = .done narrowed heap) ∧
    SourceEqualityRequiredCache.Keeps sourceHeap heap ∧
    Available heap narrowed ∧ narrowed.free = [] ∧
    let initial : Machine Symbol Guard := ⟨heap, domains⟩
    ∃ final : Machine Symbol Guard,
      execute top SourceEqualityPCSNativeEdge.conjoin 13 IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
          .done (.mu entry body depth ordinary) final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap final.heap ∧
      Extension initial final ∧ Covered [] final.heap ∧
      Available final.heap (.mu entry body depth ordinary) ∧ Available final.heap rootValue ∧
      Available final.heap narrowed ∧
      final.heap.nodeRecords key = some (.mu entry body depth ordinary) ∧
      (∀ extra, execute top SourceEqualityPCSNativeEdge.conjoin (13 + extra) IntersectionEmptyDomain.emptyDomain
        (.reference (.interned entry.identity)) (.mu entry body depth ordinary) initial =
          .done (.mu entry body depth ordinary) final) := by
  have checked := InternedFreshOrdinaryFacts.closed_verified (ordinarySymbols whole)
  have rootAvailable : Available sourceHeap rootValue := checked.result rootValue sourceHeap built
  have rootClosed := InternedFreshOrdinarySourceFreeNames.closed_free_empty
    (ordinarySymbols whole) rootValue sourceHeap built
  have sourceReady := SourceEqualityRequiredCache.constructed
    (ordinarySymbols whole) rootValue sourceHeap built
  obtain ⟨bound, ownResult, ownAfter, _ownRun, ownKept, ownAvailable, ownClosed, ownStable⟩ :=
    SourcePruningOuterNarrow.narrow_complete holeKey fits admits metadata 0 rootValue sourceHeap
      sourceReady rootAvailable rootClosed
  have actualAtSum := narrow_done_moreFuel holeKey fits admits metadata fuel bound 0 rootValue sourceHeap
    narrowed heap observed
  have ownAtSum : SourcePruningOuterNarrow.narrow holeKey fits admits metadata
      (fuel + bound) 0 rootValue sourceHeap = .done ownResult ownAfter := by
    simpa only [Nat.add_comm] using ownStable fuel
  have same := MergedSourceComparison.Result.done.inj (actualAtSum.symm.trans ownAtSum)
  have kept : SourceEqualityRequiredCache.Keeps sourceHeap heap := by
    rw [same.2]
    exact ownKept
  have narrowedAvailable : Available heap narrowed := by
    rw [same.1, same.2]
    exact ownAvailable
  have narrowedClosed : narrowed.free = [] := by
    rw [same.1]
    exact ownClosed
  have facts : Facts heap := kept.ready.semantic.1.normal.facts
  obtain ⟨final, done, valid, extension, universeAvailable, rootAvailableFinal, retained, stable,
      retainedCoverage, retainedSemantic⟩ :=
    SourceSynthesisCurrentUniverseReferenceIdentity.current_stored_universe_reference_identity_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts kept.growth domains cacheValid
  refine ⟨(fun extra => narrow_done_moreFuel holeKey fits admits metadata fuel extra 0 rootValue sourceHeap
      narrowed heap observed), kept, narrowedAvailable, narrowedClosed, final, done, valid,
    retainedSemantic kept.ready.semantic, extension, retainedCoverage [] kept.ready.covered,
    universeAvailable, rootAvailableFinal, extension.available _ narrowedAvailable, retained, stable⟩

end MicroCFTA.SourceSynthesisCurrentUniverseRootNarrowIdentity
