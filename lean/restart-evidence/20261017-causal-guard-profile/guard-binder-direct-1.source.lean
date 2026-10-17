import MicroCFTA.SourceCurrentConstrainedCapGuardNative

/-!
# Finite optional binders with actual warm guard readback

The initial body has a finite cap and a positive ranked classifier. Its free
names exclude the two probe kinds. Actual callbacks construct both probes.
The actual selected record supplies the returned guard and occurrence laws,
including an earlier first writer. No completed callback is an input.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGuardBinder
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Outcome request)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPairOccurrences (Classified)
open SourceCurrentConstrainedCapPairOccurrenceCallbacks (mark)
open SourceCurrentConstrainedCapGuardHeap (Heap)
open SourceEqualityRequiredCache (Ready Keeps)
variable {Symbol Guard : Type}

/-- Initial capped and classified input produces the same finite optional binder and every returned invariant. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (pair : Nat × Nat) (body : Value Symbol Guard) (state : State Symbol Guard)
    (ready : Ready state) (available : Available state body) (bounded : Cap annotation depth body)
    (guards : Heap annotation state) (weight : Reference → Nat) (bound : Nat) (positive : 0 < bound)
    (oldWeight : weight (.intersection pair.1 pair.2) = bound) (classified : Classified weight bound body)
    (depthFresh : .depth ∉ body.free) (ordinaryFresh : ∀ level, .uninterned level ∉ body.free) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after ∧
      Cap annotation depth value ∧ Classified weight bound value ∧ Heap annotation after ∧
      SourceCurrentHereditaryConstruction.MuStored annotation after ∧ Available after value ∧ Keeps state after := by
  by_cases used : Reference.intersection pair.1 pair.2 ∈ body.free
  · let old := Reference.intersection pair.1 pair.2
    obtain ⟨probe, afterProbe, probeDone, probeCap, probeClassified, _probeStored, probeAvailable, probeKeeps, _probeLocal⟩ :=
      SourceCurrentConstrainedCapNativeCallbacks.complete annotation depth body old .depth state ready available
        (InternedNestedProvenance.depth_available state) bounded
        (SourceCurrentConstrainedCapGuardNative.stored annotation state guards) weight bound oldWeight classified depthFresh
    have probeGuards : Heap annotation afterProbe := by
      simpa only [probeDone, Outcome.state] using
        (SourceCurrentConstrainedCapGuardNative.native_callback annotation body old .depth state ready.semantic available
          (InternedNestedProvenance.depth_available state) guards).heap
    have bodyAvailableProbe := probeKeeps.available body available
    obtain ⟨ordinary, afterOrdinary, ordinaryDone, ordinaryCap, ordinaryClassified, _ordinaryStored,
      ordinaryAvailable, ordinaryKeeps, _ordinaryLocal⟩ :=
      SourceCurrentConstrainedCapNativeCallbacks.complete annotation depth body old
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel probe)) afterProbe probeKeeps.ready bodyAvailableProbe
        (InternedNestedProvenance.ordinary_available afterProbe _) bounded
        (SourceCurrentConstrainedCapGuardNative.stored annotation afterProbe probeGuards)
        weight bound oldWeight classified (ordinaryFresh _)
    obtain ⟨value, after, actual, semantic, finalGuards, covered, output, growth, history⟩ :=
      SourceCurrentConstrainedCapGuardNative.complete annotation pair body state ready.semantic available ready.covered guards
    have requested : request true probe ordinary (SourceRecursiveIntersectionMaybeMu.callback old body) afterOrdinary =
        .done value after := by
      simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu, used, if_pos, SourceRecursiveIntersectionMaybeMu.construct,
        probeDone, ordinaryDone, Outcome.bind, old] using actual
    have bodyAvailableOrdinary := ordinaryKeeps.available body bodyAvailableProbe
    have probeAvailableOrdinary := ordinaryKeeps.available probe probeAvailable
    have physical := InternedNestedRequestFacts.request_verified true probe ordinary
      (SourceRecursiveIntersectionMaybeMu.callback old body) afterOrdinary ordinaryKeeps.ready.semantic.1.normal.facts
      probeAvailableOrdinary ordinaryAvailable (by
        intro marker current currentGrowth currentHistory currentFacts markerAvailable
        exact SourceCurrentConstrainedCapCallbackCertificates.verified body old marker current currentFacts
          (bodyAvailableOrdinary.grows afterOrdinary current currentGrowth currentHistory) markerAvailable)
    have finalProbe : Available after probe := by
      simpa only [requested, Outcome.state] using physical.available probe probeAvailableOrdinary
    have finalOrdinary : Available after ordinary := by
      simpa only [requested, Outcome.state] using physical.available ordinary ordinaryAvailable
    obtain ⟨winner, present, result⟩ := SourceCurrentConstrainedCapGuardNative.request_record true probe ordinary
      (SourceRecursiveIntersectionMaybeMu.callback old body) afterOrdinary value after requested
    have unused := SourceCurrentConstrainedCapWarmOccurrences.ordinary_unused weight bound probe ordinary positive ordinaryClassified
    have capped := SourceCurrentConstrainedCapGuardReadback.hit_cap annotation depth probe ordinary winner after
      semantic.1.normal.facts finalProbe finalOrdinary semantic.2 finalGuards present unused ordinaryCap
    have ranked := SourceCurrentConstrainedCapWarmOccurrences.hit_classified weight bound probe ordinary winner after
      semantic finalProbe finalOrdinary present positive probeClassified ordinaryClassified
    have oldDepth : InternedOpenDepthReadback.Heap
        (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state := by
      rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair body state state ready.semantic.1.normal.facts available]
      rw [if_pos used]
      exact (InternedOpenDepthExecution.build_depth _ _ state
        (SourceRecursiveIntersectionSemanticHeap.context state ready.semantic _
          (InternedStoredSubstitution.leaves_available body state available)) ready.semantic.2 ready.depth).heap
    have finalReady : Ready after := ⟨semantic, covered, by simpa only [actual, Outcome.state] using oldDepth⟩
    exact ⟨value, after, actual, result ▸ capped, result ▸ ranked, finalGuards,
      SourceCurrentConstrainedCapGuardNative.stored annotation after finalGuards, output, ⟨finalReady, growth, history⟩⟩
  · exact ⟨body, state, SourceRecursiveIntersectionMaybeMu.unused pair body state used, bounded, classified, guards,
      SourceCurrentConstrainedCapGuardNative.stored annotation state guards, available,
      SourceEqualityRequiredCache.pure_keeps state ready⟩

/-- Intersection-only initial free support supplies the exact two probe-freshness premises. -/
theorem intersection_complete [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (pair : Nat × Nat) (body : Value Symbol Guard) (state : State Symbol Guard)
    (ready : Ready state) (available : Available state body) (bounded : Cap annotation depth body)
    (guards : Heap annotation state) (weight : Reference → Nat) (bound : Nat) (positive : 0 < bound)
    (oldWeight : weight (.intersection pair.1 pair.2) = bound) (classified : Classified weight bound body)
    (support : ∀ name ∈ body.free, ∃ first second, name = .intersection first second) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after ∧
      Cap annotation depth value ∧ Classified weight bound value ∧ Heap annotation after ∧
      SourceCurrentHereditaryConstruction.MuStored annotation after ∧ Available after value ∧ Keeps state after := by
  apply complete annotation depth pair body state ready available bounded guards weight bound positive oldWeight classified
  · intro member
    obtain ⟨first, second, impossible⟩ := support .depth member
    cases impossible
  · intro level member
    obtain ⟨first, second, impossible⟩ := support (.uninterned level) member
    cases impossible

end MicroCFTA.SourceCurrentConstrainedCapGuardBinder
