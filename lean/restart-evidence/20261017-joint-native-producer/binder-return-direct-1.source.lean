import MicroCFTA.SourceCurrentConstrainedCapNativeProbeSupport

/-!
# Actual optional-binder return laws during native execution

These verifiers need the current semantic heap, not complete-cache coverage.
They inspect a literal completed optional binder. Every probe fact comes
from its actual earlier callback. The final first writer supplies the warm
body law. An enclosing completion proof must construct its own execution.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeBinderReturn
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Outcome request)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPairOccurrences (Classified)
open SourceCurrentConstrainedCapGuardHeap (Heap)
open SourceCurrentConstrainedCapNativeProbeSupport (ProbeFree)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
variable {Symbol Guard : Type}

private theorem effects [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    (pair : Nat × Nat) (body : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (available : Available state body) (guards : Heap annotation state)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after) :
    Heap annotation after ∧ SourceCurrentHereditaryConstruction.MuStored annotation after ∧
      Available after value ∧ SemanticHeap after ∧ Grows state after ∧ Extends state.nodes.issued after.nodes.issued := by
  have retained : Heap annotation after := by
    simpa only [actual, Outcome.state] using
      SourceCurrentConstrainedCapGuardNative.optional_heap annotation pair body state semantic available guards
  have physical := SourceRecursiveIntersectionMaybeMu.verified pair body state semantic.1.normal.facts available
  have finalSemantic : SemanticHeap after := by
    simpa only [actual, Outcome.state] using
      SourceRecursiveIntersectionMaybeMu.semantic_context pair body state semantic.1 available semantic.2
  exact ⟨retained, SourceCurrentConstrainedCapGuardNative.stored annotation after retained,
    physical.result value after actual, finalSemantic,
    by simpa only [actual, Outcome.state] using physical.growth,
    by simpa only [actual, Outcome.state] using physical.history⟩

/-- An actual positive-rank return derives its cap and classifier without a complete-cache premise. -/
theorem positive [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (pair : Nat × Nat) (body : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (available : Available state body) (bounded : Cap annotation depth body)
    (guards : Heap annotation state) (weight : Reference → Nat) (bound : Nat) (nonzero : 0 < bound)
    (oldWeight : weight (.intersection pair.1 pair.2) = bound) (classified : Classified weight bound body)
    (fresh : ProbeFree body) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after) :
    Cap annotation depth value ∧ Classified weight bound value ∧ Heap annotation after ∧
      SourceCurrentHereditaryConstruction.MuStored annotation after ∧ Available after value ∧
      SemanticHeap after ∧ Grows state after ∧ Extends state.nodes.issued after.nodes.issued ∧ ProbeFree value := by
  have physical := effects annotation pair body state semantic available guards value after actual
  have finalFresh := SourceCurrentConstrainedCapNativeProbeSupport.optionalBinder pair body state semantic.1
    available fresh value after actual
  suffices cappedRanked : Cap annotation depth value ∧ Classified weight bound value from
    ⟨cappedRanked.1, cappedRanked.2, physical.1, physical.2.1, physical.2.2.1,
      physical.2.2.2.1, physical.2.2.2.2.1, physical.2.2.2.2.2, finalFresh⟩
  by_cases used : Reference.intersection pair.1 pair.2 ∈ body.free
  · let old := Reference.intersection pair.1 pair.2
    have sequence := actual
    simp only [SourceRecursiveIntersectionMaybeMu.maybeMu, used, ite_true,
      SourceRecursiveIntersectionMaybeMu.construct] at sequence
    cases depthDone : SourceRecursiveIntersectionMaybeMu.callback old body .depth state with
    | pending key stopped => simp only [depthDone, Outcome.bind] at sequence; cases sequence
    | done probe afterProbe =>
        have depthChecked := SourceCurrentConstrainedCapCallbackCertificates.checked annotation depth body old .depth state
          semantic available (InternedNestedProvenance.depth_available state) bounded
          (SourceCurrentConstrainedCapGuardNative.stored annotation state guards)
          weight bound oldWeight classified fresh.depth
        have probeClassified := (depthChecked.result probe afterProbe depthDone).2.1
        have depthPhysical := SourceCurrentConstrainedCapCallbackCertificates.verified body old .depth state
          semantic.1.normal.facts available (InternedNestedProvenance.depth_available state)
        have probeAvailable := depthPhysical.result probe afterProbe depthDone
        have bodyAvailableProbe : Available afterProbe body := by
          simpa only [depthDone, Outcome.state] using depthPhysical.available body available
        have probeSemantic : SemanticHeap afterProbe := by
          simpa only [depthDone, Outcome.state] using SourceCurrentConstrainedCapCallbackCertificates.semantic body old .depth
            state semantic available (InternedNestedProvenance.depth_available state)
        have probeGuards : Heap annotation afterProbe := by
          simpa only [depthDone, Outcome.state] using
            (SourceCurrentConstrainedCapGuardNative.native_callback annotation body old .depth state semantic available
              (InternedNestedProvenance.depth_available state) guards).heap
        cases ordinaryDone : SourceRecursiveIntersectionMaybeMu.callback old body
            (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel probe)) afterProbe with
        | pending key stopped => simp only [depthDone, ordinaryDone, Outcome.bind] at sequence; cases sequence
        | done ordinary afterOrdinary =>
            have ordinaryChecked := SourceCurrentConstrainedCapCallbackCertificates.checked annotation depth body old
              (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel probe)) afterProbe probeSemantic bodyAvailableProbe
              (InternedNestedProvenance.ordinary_available afterProbe _) bounded
              (SourceCurrentConstrainedCapGuardNative.stored annotation afterProbe probeGuards)
              weight bound oldWeight classified (fresh.ordinary _)
            have ordinaryResult := ordinaryChecked.result ordinary afterOrdinary ordinaryDone
            have ordinaryPhysical := SourceCurrentConstrainedCapCallbackCertificates.verified body old
              (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel probe)) afterProbe probeSemantic.1.normal.facts
              bodyAvailableProbe (InternedNestedProvenance.ordinary_available afterProbe _)
            have ordinarySemantic : SemanticHeap afterOrdinary := by
              simpa only [ordinaryDone, Outcome.state] using SourceCurrentConstrainedCapCallbackCertificates.semantic body old
                (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel probe)) afterProbe probeSemantic bodyAvailableProbe
                (InternedNestedProvenance.ordinary_available afterProbe _)
            have requested : request true probe ordinary (SourceRecursiveIntersectionMaybeMu.callback old body) afterOrdinary =
                .done value after := by simpa only [depthDone, ordinaryDone, Outcome.bind, old] using sequence
            have originalAvailable : Available afterOrdinary body := by
              simpa only [ordinaryDone, Outcome.state] using ordinaryPhysical.available body bodyAvailableProbe
            have probeAvailableOrdinary : Available afterOrdinary probe := by
              simpa only [ordinaryDone, Outcome.state] using ordinaryPhysical.available probe probeAvailable
            have ordinaryAvailable := ordinaryPhysical.result ordinary afterOrdinary ordinaryDone
            have requestPhysical := InternedNestedRequestFacts.request_verified true probe ordinary
              (SourceRecursiveIntersectionMaybeMu.callback old body) afterOrdinary ordinarySemantic.1.normal.facts
              probeAvailableOrdinary ordinaryAvailable (by
                intro marker current growth history currentFacts markerAvailable
                exact SourceCurrentConstrainedCapCallbackCertificates.verified body old marker current currentFacts
                  (originalAvailable.grows afterOrdinary current growth history) markerAvailable)
            have finalProbe : Available after probe := by
              simpa only [requested, Outcome.state] using requestPhysical.available probe probeAvailableOrdinary
            have finalOrdinary : Available after ordinary := by
              simpa only [requested, Outcome.state] using requestPhysical.available ordinary ordinaryAvailable
            obtain ⟨winner, present, result⟩ := SourceCurrentConstrainedCapGuardNative.request_record true probe ordinary
              (SourceRecursiveIntersectionMaybeMu.callback old body) afterOrdinary value after requested
            have unused := SourceCurrentConstrainedCapWarmOccurrences.ordinary_unused weight bound probe ordinary nonzero ordinaryResult.2.1
            have capped := SourceCurrentConstrainedCapGuardReadback.hit_cap annotation depth probe ordinary winner after
              physical.2.2.2.1.1.normal.facts finalProbe finalOrdinary physical.2.2.2.1.2 physical.1 present unused ordinaryResult.1
            have ranked := SourceCurrentConstrainedCapWarmOccurrences.hit_classified weight bound probe ordinary winner after
              physical.2.2.2.1 finalProbe finalOrdinary present nonzero probeClassified ordinaryResult.2.1
            exact ⟨result ▸ capped, result ▸ ranked⟩
  · have same := SourceRecursiveIntersectionMaybeMu.unused pair body state used
    rw [same] at actual
    cases actual
    exact ⟨bounded, classified⟩

/-- A hereditary actual return has cap at every depth and retains its zero-rank classifier. -/
theorem zero [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (pair : Nat × Nat) (body : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticHeap state) (available : Available state body)
    (annotated : SourceEqualityAnnotationLanguage.Annotated annotation body) (guards : Heap annotation state)
    (weight : Reference → Nat) (classified : Classified weight 0 body) (fresh : ProbeFree body)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after) :
    Cap annotation depth value ∧ Classified weight 0 value ∧ Heap annotation after ∧
      SourceCurrentHereditaryConstruction.MuStored annotation after ∧ Available after value ∧
      SemanticHeap after ∧ Grows state after ∧ Extends state.nodes.issued after.nodes.issued ∧ ProbeFree value := by
  have physical := effects annotation pair body state semantic available guards value after actual
  have checked := SourceCurrentHereditaryConstruction.optionalBinder annotation pair body state semantic.1.normal.facts available
    annotated (SourceCurrentConstrainedCapGuardNative.stored annotation state guards)
  have result := checked.result value after actual
  have names := SourceRecursiveIntersectionMaybeMu.free_support pair body state semantic.1 available value after actual
  have ranked : Classified weight 0 value :=
    ⟨fun name member => classified.free name (names name member).1, fun _ _ => .inr rfl⟩
  exact ⟨.plain depth result, ranked, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2.1,
    physical.2.2.2.2.1, physical.2.2.2.2.2,
    SourceCurrentConstrainedCapNativeProbeSupport.optionalBinder pair body state semantic.1 available fresh value after actual⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeBinderReturn
