import MicroCFTA.SourceCurrentOriginalRowPhysicalMeaning

namespace MicroCFTA.SourceCurrentOriginalRowDeletionSoundness
open Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open InternedEdgeResidency SourceRecursiveIntersectionInputView
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard

/-- Each tested result identity gives physical inclusion in the other original row. -/
theorem deletion_sound
    (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool)
    (inputModel : InputMeaning (view source holds))
    (inputRanked : RankedInput (view source holds) inputModel.valid)
    (parent : Value Symbol Guard)
    (original : OriginalInput source (inputOf parent))
    (available : Available source parent)
    (closed : parent.free = [])
    (admitted : inputModel.valid (inputOf parent))
    (pivot candidate : Edge)
    (pivotMember : pivot ∈ nodeEdges parent)
    (candidateMember : candidate ∈ nodeEdges parent)
    (finalHeap : InternedConstructorTemplates.State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent finalHeap)
    (growth : Grows source finalHeap)
    (common : Edge)
    (resident : EdgeResident finalHeap common)
    (law :
      let ordered := if candidate.entry.identity < pivot.entry.identity
        then (candidate, pivot) else (pivot, candidate)
      SourceCurrentAllocatedNativeContextCache.EdgeLaw
        (view source holds) inputModel inputRanked holds
        ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩ common) :
    (common.entry.identity = candidate.entry.identity →
      ∀ ambient : InternedGuardedLanguage.Env Symbol,
        BinderLanguage.Included
          (InternedGuardedLanguage.edgeMeaning holds ambient candidate)
          (InternedGuardedLanguage.edgeMeaning holds ambient pivot)) ∧
    (common.entry.identity = pivot.entry.identity →
      ∀ ambient : InternedGuardedLanguage.Env Symbol,
        BinderLanguage.Included
          (InternedGuardedLanguage.edgeMeaning holds ambient pivot)
          (InternedGuardedLanguage.edgeMeaning holds ambient candidate)) := by
  obtain ⟨pivotInputs, pivotMeaning⟩ :=
    SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning source facts holds inputModel
      parent pivot original available closed admitted pivotMember
  obtain ⟨candidateInputs, candidateMeaning⟩ :=
    SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning source facts holds inputModel
      parent candidate original available closed admitted candidateMember
  have pivotResident : EdgeResident finalHeap pivot :=
    edge_grows source finalHeap growth pivot
      (resident_edges source facts.linked parent available.resident pivot pivotMember)
  have candidateResident : EdgeResident finalHeap candidate :=
    edge_grows source finalHeap growth candidate
      (resident_edges source facts.linked parent available.resident candidate candidateMember)
  have commonSound (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
      (accepted : InternedGuardedLanguage.edgeMeaning holds ambient common term) :
      InternedGuardedLanguage.edgeMeaning holds ambient pivot term ∧
        InternedGuardedLanguage.edgeMeaning holds ambient candidate term := by
    by_cases swapped : candidate.entry.identity < pivot.entry.identity
    · have canonicalLaw : SourceCurrentAllocatedNativeContextCache.EdgeLaw
          (view source holds) inputModel inputRanked holds
          ⟨IntersectionEmptyDomain.emptyDomain, candidate, pivot⟩ common := by
        simpa only [swapped, ↓reduceIte] using law
      have both : SourceCurrentAllocatedNativeContextCache.RowLanguage
          holds inputModel.languages candidate term ∧
          SourceCurrentAllocatedNativeContextCache.RowLanguage
            holds inputModel.languages pivot term :=
        canonicalLaw.sound ⟨candidateInputs, pivotInputs⟩ ambient
          (SourceCurrentAllocatedNativePairContexts.sound_empty_domain
            inputModel.languages ambient) term accepted
      rw [candidateMeaning ambient, pivotMeaning ambient] at both
      exact both.symm
    · have canonicalLaw : SourceCurrentAllocatedNativeContextCache.EdgeLaw
          (view source holds) inputModel inputRanked holds
          ⟨IntersectionEmptyDomain.emptyDomain, pivot, candidate⟩ common := by
        simpa only [swapped, ↓reduceIte] using law
      have both : SourceCurrentAllocatedNativeContextCache.RowLanguage
          holds inputModel.languages pivot term ∧
          SourceCurrentAllocatedNativeContextCache.RowLanguage
            holds inputModel.languages candidate term :=
        canonicalLaw.sound ⟨pivotInputs, candidateInputs⟩ ambient
          (SourceCurrentAllocatedNativePairContexts.sound_empty_domain
            inputModel.languages ambient) term accepted
      rw [pivotMeaning ambient, candidateMeaning ambient] at both
      exact both
  constructor
  · intro same ambient term accepted
    have samePayload : common = candidate :=
      edge_identity_unique finalHeap coherent common candidate resident candidateResident same
    have commonAccepted : InternedGuardedLanguage.edgeMeaning holds ambient common term := by
      rw [samePayload]
      exact accepted
    exact (commonSound ambient term commonAccepted).1
  · intro same ambient term accepted
    have samePayload : common = pivot :=
      edge_identity_unique finalHeap coherent common pivot resident pivotResident same
    have commonAccepted : InternedGuardedLanguage.edgeMeaning holds ambient common term := by
      rw [samePayload]
      exact accepted
    exact (commonSound ambient term commonAccepted).2

end MicroCFTA.SourceCurrentOriginalRowDeletionSoundness

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentOriginalRowDeletionSoundness.deletion_sound
#print MicroCFTA.SourceCurrentOriginalRowDeletionSoundness.deletion_sound
#print axioms MicroCFTA.SourceCurrentOriginalRowDeletionSoundness.deletion_sound
