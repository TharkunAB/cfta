import MicroCFTA.SourceSynthesisCurrentUniverseStartupAtoms
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness

namespace MicroCFTA.SourceSynthesisCurrentUniverseClosedMuClassification
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBoundaryAtoms
open InternedBinderProtocol (NodeKey NodeRef)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- A closed Mu with only the source universe atom is the full original Mu value. -/
theorem current_stored_universe_closed_mu_eq_after_growth
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (facts : Facts heap) (growth : Grows sourceHeap heap)
    (other : Interned NodeKey) (otherBody otherDepth otherOrdinary : Value Symbol Guard)
    (available : Available heap (.mu other otherBody otherDepth otherOrdinary))
    (closed : (Value.mu other otherBody otherDepth otherOrdinary).free = [])
    (onlyU : ∀ atom ∈ atoms (.mu other otherBody otherDepth otherOrdinary),
      atom = .mu entry.identity) :
    Value.mu other otherBody otherDepth otherOrdinary = .mu entry body depth ordinary := by
  have originalAvailable : Available heap (.mu entry body depth ordinary) :=
    facts.cached.nodes key _ (growth.nodeRecords key _ stored)
  have originalClosed : (Value.mu entry body depth ordinary).free = [] :=
    SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      heap facts growth (.mu entry body depth ordinary) originalAvailable
      (by
        intro atom occurrence
        simpa only [atoms, List.mem_singleton] using occurrence)
  have sameAtom : NodeRef.mu other.identity = .mu entry.identity :=
    onlyU (.mu other.identity) (by simp only [atoms, List.mem_singleton])
  have sameIdentity : other.identity = entry.identity := NodeRef.mu.inj sameAtom
  exact SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective
    heap facts (.mu other otherBody otherDepth otherOrdinary) (.mu entry body depth ordinary)
    available originalAvailable closed originalClosed entry.identity
    (by simp only [SourceRecursiveIntersectionControl.identity, sameIdentity]) rfl

end MicroCFTA.SourceSynthesisCurrentUniverseClosedMuClassification
