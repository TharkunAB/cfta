import MicroCFTA.SourceSynthesisCurrentCanonicalUnionTypeMember
import MicroCFTA.SourcePruningEnumerationDischargeBoundary
import MicroCFTA.SourcePruningEnumerationIdentity

/-!
# Type choices in actual done pending domains

The native done test leaves Mu and Union boundaries in graph-bearing slots.
Actual only-U atoms and union normality identify an original-U alternative.
Every finite TypeIn choice belongs to each such actual domain handle.
This result needs the structural facts at the actual endpoint.
It does not derive them from a complete source worker history.
-/
namespace MicroCFTA.SourceSynthesisCurrentDonePendingTypes
open Language Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedStoredMuOrigins (Normal)
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationNativeLanguage (handles)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false
variable {Typing : Type} {width : Nat}

/-- Every finite source Type belongs to an actual closed canonical only-U boundary. -/
theorem recursive_boundary_original_universe_type_members
    [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (normal : Normal heap)
    (irreducible : SourceCurrentRequiredUnionNormal.UnionNormal heap)
    (growth : Grows sourceHeap heap) (value : Value Symbol Guard)
    (available : Available heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (onlyU : ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) :
    ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
      ∀ term, TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query) term →
        handles (SourceEqualityPCSGuard.holds formulas solver) ambient heap handle term := by
  cases value with
  | empty | reference _ | node _ _ _ _ =>
      simp only [MergedOrdinaryHeight.recursiveBoundary] at boundary
  | mu other otherBody otherDepth otherOrdinary =>
      have same :=
        SourceSynthesisCurrentUniverseClosedMuClassification.current_stored_universe_closed_mu_eq_after_growth
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          heap normal.facts growth other otherBody otherDepth otherOrdinary available closed onlyU
      obtain ⟨handle, encoded, readback⟩ := SourcePruningEnumerationNodes.available_readback
        heap (.mu other otherBody otherDepth otherOrdinary) normal.facts.coherent available closed
      obtain ⟨_sourceAvailable, _sourceClosed, originalLanguage⟩ :=
        SourceSynthesisCurrentNativeUniverseMembership.original_stored_universe_language
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      refine ⟨handle, encoded, readback, ?_⟩
      intro term typed
      apply (SourcePruningEnumerationNativeLanguage.handles_lookup
        (SourceEqualityPCSGuard.holds formulas solver) ambient heap handle
        (.mu other otherBody otherDepth otherOrdinary) term readback).mpr
      rw [same, originalLanguage]
      exact typed.member (SourceEqualityPCSGuard.holds formulas solver)
        (SourceEqualityPCSConstructors.top_true formulas solver)
  | union unionEntry members unionDepth unionFree =>
      obtain ⟨_originalMember, handle, encoded, readback, members⟩ :=
        SourceSynthesisCurrentCanonicalUnionTypeMember.grown_union_original_universe_type_members
          formulas solver ambient lib query signed whole accepted rootValue sourceHeap built
          key entry body depth ordinary stored heap normal irreducible growth
          unionEntry members unionDepth unionFree available onlyU
      exact ⟨handle, encoded, readback, members⟩

/-- Actual done slots admit all finite Type choices under their endpoint atom invariant. -/
theorem done_pending_type_members
    [DecidableEq FullSyntax.Formula] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (caller : SourceCurrentAllocatedPartialState.State width)
    (before : EnumerationExpandableIndex.Cached Symbol Guard)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (done : SourcePruningEnumerationRestart.decision none order metadata before = some .done)
    (normal : Normal caller.checked.native.machine.heap)
    (irreducible : SourceCurrentRequiredUnionNormal.UnionNormal caller.checked.native.machine.heap)
    (growth : Grows sourceHeap caller.checked.native.machine.heap)
    (onlyU : ∀ slot handle scs,
      before.core.values[slot]? = some (.unenumerated (some handle) scs) →
      ∀ value, lookupNode caller.checked.native.machine.heap handle = some value →
      ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) :
    ∀ slot handle scs, before.core.values[slot]? = some (.unenumerated (some handle) scs) →
      scs = [] ∧ ∀ term, TypeIn (SourceSynthesisCurrentContext.constructorCatalog lib query) term →
        handles (SourceEqualityPCSGuard.holds formulas solver) ambient
          caller.checked.native.machine.heap handle term := by
  intro slot handle scs atSlot
  obtain ⟨value, decoded, available, closed, boundary, emptyBucket⟩ :=
    SourcePruningEnumerationRestart.done_pending_boundary order metadata caller before
      valid done slot handle scs atSlot
  obtain ⟨actualHandle, encoded, _readback, members⟩ :=
    recursive_boundary_original_universe_type_members formulas solver ambient lib query signed whole
      accepted rootValue sourceHeap built key entry body depth ordinary stored
      caller.checked.native.machine.heap normal irreducible growth value available closed boundary
      (onlyU slot handle scs atSlot value decoded)
  have actualEncoding := SourcePruningEnumerationIdentity.lookup_encode caller.checked.native.machine.heap
    handle value normal.facts.coherent decoded
  have same : actualHandle = handle := Option.some.inj (encoded.symm.trans actualEncoding)
  subst actualHandle
  exact ⟨emptyBucket, members⟩

end MicroCFTA.SourceSynthesisCurrentDonePendingTypes

#check @MicroCFTA.SourceSynthesisCurrentDonePendingTypes.recursive_boundary_original_universe_type_members
#print axioms MicroCFTA.SourceSynthesisCurrentDonePendingTypes.recursive_boundary_original_universe_type_members
#check @MicroCFTA.SourceSynthesisCurrentDonePendingTypes.done_pending_type_members
#print axioms MicroCFTA.SourceSynthesisCurrentDonePendingTypes.done_pending_type_members
