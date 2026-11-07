import MicroCFTA.SourceSynthesisUniverseColdResidentRows
import MicroCFTA.SourceSynthesisUniverseProbeReconstruction
import MicroCFTA.SourceRecursiveIntersectionMaybeMu

/-!
# Original synthesis inputs replay both stored universe probes

The actual cold constructor supplies the original body and both probes.
Their raw row records remain resident in its returned cache. The actual
stored executor and normalized source callbacks return the original probe
values in that cache. Neither replay allocates a new record.
The intersection product's callbacks remain a separate composition step.
-/
namespace MicroCFTA.SourceSynthesisUniverseStoredProbeInput
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome work)
open InternedStoredSubstitutionRebind (replacement)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)

variable [DecidableEq (EdgeKey String Guard)]

/-- Original library and query data derive exact replay of the stored body's two original probes. -/
theorem typesOf_stored_probes (lib : Library) (query : Query) :
    ∃ entry body depth ordinary heap,
      InternedFreshOrdinaryConstruction.build (SourceSynthesisFirstOrderConstruction.typesOf lib query)
        [] empty = .done (.mu entry body depth ordinary) heap ∧
      Facts heap ∧ Available heap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned entry.identity) body ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      InternedFreshOrdinaryStoredSubstitution.execute body
        (replacement (.interned entry.identity) (.reference .depth)) heap = .done depth heap ∧
      InternedFreshOrdinaryStoredSubstitution.execute body
        (replacement (.interned entry.identity)
          (.reference (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)))) heap =
        .done ordinary heap ∧
      SourceRecursiveIntersectionMaybeMu.callback (.interned entry.identity) body .depth heap = .done depth heap ∧
      SourceRecursiveIntersectionMaybeMu.callback (.interned entry.identity) body
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) heap = .done ordinary heap ∧
      SourceRecursiveIntersectionMaybeMu.construct (.interned entry.identity) body heap =
        .done (.mu entry body depth ordinary) heap := by
  let catalog := SourceSynthesisFirstOrderConstruction.constructorCatalog lib query
  obtain ⟨entry, body, depth, ordinary, heap, built, facts, available, shape,
      bodyRows, depthRows, ordinaryRows, bodyAvailable, depthAvailable, ordinaryAvailable⟩ :=
    SourceSynthesisUniverseColdResidentRows.allTypes_cold_rows top catalog
  have depthDone := SourceSynthesisUniverseProbeReconstruction.execute_probe top catalog
    (.interned entry.identity) .depth body depth heap facts bodyAvailable depthAvailable bodyRows depthRows
  have ordinaryDone := SourceSynthesisUniverseProbeReconstruction.execute_probe top catalog
    (.interned entry.identity) (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth))
    body ordinary heap facts bodyAvailable ordinaryAvailable bodyRows ordinaryRows
  have originalShape := shape
  obtain ⟨_, _, _, _, bodyEq, _⟩ := shape
  have closed : (Value.mu entry body depth ordinary).free = [] := by simp [Value.free, bodyEq]
  obtain ⟨_, _, _, _, depthEq, _⟩ := depthRows
  obtain ⟨_, _, _, _, ordinaryEq, _⟩ := ordinaryRows
  have depthCallback : SourceRecursiveIntersectionMaybeMu.callback (.interned entry.identity) body .depth heap =
      .done depth heap := by
    simp only [SourceRecursiveIntersectionMaybeMu.callback, depthDone, Outcome.bind, depthEq,
      withoutSelfReference, work, run]
  have ordinaryCallback : SourceRecursiveIntersectionMaybeMu.callback (.interned entry.identity) body
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) heap = .done ordinary heap := by
    simp only [SourceRecursiveIntersectionMaybeMu.callback, ordinaryDone, Outcome.bind, ordinaryEq,
      withoutSelfReference, work, run]
  obtain ⟨_, table, record⟩ := SourceSynthesisUniverseNativeInput.available_mu_key_readback
    heap facts entry body depth ordinary available
  have finished := SourceSynthesisUniverseColdReadback.finish_shaped_mu
    top catalog entry body depth ordinary originalShape
  have recovered : SourceRecursiveIntersectionMaybeMu.construct (.interned entry.identity) body heap =
      .done (.mu entry body depth ordinary) heap := by
    simp only [SourceRecursiveIntersectionMaybeMu.construct, depthCallback, Outcome.bind, ordinaryCallback,
      InternedNestedConstruction.request, table, record, finished]
  exact ⟨entry, body, depth, ordinary, heap, built, facts, available, originalShape, closed,
    depthDone, ordinaryDone, depthCallback, ordinaryCallback, recovered⟩

end MicroCFTA.SourceSynthesisUniverseStoredProbeInput
