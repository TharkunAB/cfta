import MicroCFTA.SourceSynthesisUniverseProbeReconstruction
import MicroCFTA.SourceSynthesisUniverseNativeInput

/-!
# Complete probe and Mu identity in one actual cache

Resident universe rows at the same probe name reconstruct one value.
Available Mu records with equal probes have the same canonical key.
The actual stored record therefore identifies the complete Mu value.
No node-identity equality or cache lookup is a supplied premise.
-/
namespace MicroCFTA.SourceSynthesisUniverseProbeUniqueness
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference NodeKey)
open SourceSynthesisUniverseResidentRows (Rows)

variable {Guard : Type}

/-- Two available row packets at the same probe name identify one complete value. -/
theorem rows_unique [DecidableEq (EdgeKey String Guard)]
    (top : Guard) (catalog : List (String × Nat)) (name : Reference)
    (source target : Value String Guard) (heap : InternedConstructorTemplates.State String Guard)
    (facts : Facts heap) (sourceAvailable : Available heap source) (targetAvailable : Available heap target)
    (sourceRows : Rows top catalog name source heap) (targetRows : Rows top catalog name target heap) :
    source = target := by
  have selfDone := SourceSynthesisUniverseProbeReconstruction.execute_probe top catalog name name
    source source heap facts sourceAvailable sourceAvailable sourceRows sourceRows
  have targetDone := SourceSynthesisUniverseProbeReconstruction.execute_probe top catalog name name
    source target heap facts sourceAvailable targetAvailable sourceRows targetRows
  exact (Outcome.done.inj (selfDone.symm.trans targetDone)).1

/-- Equal complete probes select the same complete resident Mu record. -/
theorem available_mu_unique (heap : InternedConstructorTemplates.State String Guard) (facts : Facts heap)
    (leftEntry rightEntry : Interned NodeKey)
    (leftBody rightBody leftDepth rightDepth leftOrdinary rightOrdinary : Value String Guard)
    (leftAvailable : Available heap (.mu leftEntry leftBody leftDepth leftOrdinary))
    (rightAvailable : Available heap (.mu rightEntry rightBody rightDepth rightOrdinary))
    (depthSame : leftDepth = rightDepth) (ordinarySame : leftOrdinary = rightOrdinary) :
    Value.mu leftEntry leftBody leftDepth leftOrdinary = .mu rightEntry rightBody rightDepth rightOrdinary := by
  subst rightDepth rightOrdinary
  have left := SourceSynthesisUniverseNativeInput.available_mu_key_readback
    heap facts leftEntry leftBody leftDepth leftOrdinary leftAvailable
  have right := SourceSynthesisUniverseNativeInput.available_mu_key_readback
    heap facts rightEntry rightBody leftDepth leftOrdinary rightAvailable
  exact Option.some.inj (left.2.2.symm.trans right.2.2)

/-- Actual depth and selected ordinary row packets derive complete Mu identity. -/
theorem rows_mu_unique [DecidableEq (EdgeKey String Guard)]
    (top : Guard) (catalog : List (String × Nat))
    (heap : InternedConstructorTemplates.State String Guard) (facts : Facts heap)
    (leftEntry rightEntry : Interned NodeKey)
    (leftBody rightBody leftDepth rightDepth leftOrdinary rightOrdinary : Value String Guard)
    (leftAvailable : Available heap (.mu leftEntry leftBody leftDepth leftOrdinary))
    (rightAvailable : Available heap (.mu rightEntry rightBody rightDepth rightOrdinary))
    (leftDepthRows : Rows top catalog .depth leftDepth heap)
    (rightDepthRows : Rows top catalog .depth rightDepth heap)
    (leftOrdinaryRows : Rows top catalog
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel leftDepth)) leftOrdinary heap)
    (rightOrdinaryRows : Rows top catalog
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel rightDepth)) rightOrdinary heap) :
    Value.mu leftEntry leftBody leftDepth leftOrdinary = .mu rightEntry rightBody rightDepth rightOrdinary := by
  have leftDepthAvailable := leftAvailable.children leftDepth (by simp [InternedProbeProvenance.children])
  have rightDepthAvailable := rightAvailable.children rightDepth (by simp [InternedProbeProvenance.children])
  have depthSame := rows_unique top catalog .depth leftDepth rightDepth heap facts
    leftDepthAvailable rightDepthAvailable leftDepthRows rightDepthRows
  subst rightDepth
  have leftOrdinaryAvailable := leftAvailable.children leftOrdinary (by simp [InternedProbeProvenance.children])
  have rightOrdinaryAvailable := rightAvailable.children rightOrdinary (by simp [InternedProbeProvenance.children])
  have ordinarySame := rows_unique top catalog
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel leftDepth)) leftOrdinary rightOrdinary heap facts
    leftOrdinaryAvailable rightOrdinaryAvailable leftOrdinaryRows rightOrdinaryRows
  exact available_mu_unique heap facts leftEntry rightEntry leftBody rightBody leftDepth leftDepth
    leftOrdinary rightOrdinary leftAvailable rightAvailable rfl ordinarySame

end MicroCFTA.SourceSynthesisUniverseProbeUniqueness
