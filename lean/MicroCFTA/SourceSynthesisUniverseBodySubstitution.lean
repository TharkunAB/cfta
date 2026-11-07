import MicroCFTA.SourceSynthesisUniverseBodyCanonical
import MicroCFTA.SourceSynthesisUniverseStoredRows

/-!
# Actual stored substitution of the completed universe-body product

The original shape derives the marker and the source child facts. The
complete product derives its target rows and their actual final-cache hits.
Stored substitution then rebuilds those rows and the same final node without
further effects. No target list or completed substitution is supplied.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodySubstitution
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol InternedStoredClosedMuCompletion
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBody (Shape)
open SourceSynthesisUniverseBodyReferenceControl (second secondState)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- The actual body product is the final-cache replay of source substitution by its outer cutoff. -/
theorem node_substitution (top : Guard) (catalog : List (String × Nat))
    (u b : Interned NodeKey) (bodyRows : List (EdgeValue String Guard))
    (depth ordinary : Value String Guard) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (original : Machine String Guard) (facts : Facts original.heap)
    (cacheValid : Cache.Valid original.domains)
    (universeAvailable : Available original.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (shape : Shape top catalog (.interned u.identity) (.node b bodyRows 0 [.interned u.identity])) :
    ∃ value final,
      node emptyGuard conjoin
        (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
        bodyRows bodyRows (secondState u b bodyRows depth ordinary original) = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      Extension (secondState u b bodyRows depth ordinary original) final ∧
      Available final.heap value ∧ PreparedWithoutMu value ∧
      (value.free = [] ∨ value.free = [.intersection (pair u.identity u.identity).1
        (pair u.identity u.identity).2]) ∧
      InternedFreshOrdinaryStoredSubstitution.execute (.node b bodyRows 0 [.interned u.identity])
        (InternedStoredSubstitutionRebind.replacement (.interned u.identity)
          (repeatedValue (pair u.identity u.identity))) final.heap = .done value final.heap := by
  obtain ⟨value, final, _products, targets, done, finalValid, growth, available, prepared, free,
      _aligned, hits, _productResident, _retained, _targetResident, _targetLive, _exactRows, _same, pureNode⟩ :=
    SourceSynthesisUniverseBodyCanonical.node_canonical top catalog u b bodyRows depth ordinary emptyGuard
      conjoin conjoinTop original facts cacheValid universeAvailable shape
  obtain ⟨m, markerRow, _, _, _, _, _, _, _, _, _, bodyTop, bodyChildren⟩ :=
    SourceSynthesisUniverseBodyEvidence.of_shape top catalog u b bodyRows depth ordinary
      original.heap universeAvailable shape
  have originalBody : Available original.heap (.node b bodyRows 0 [.interned u.identity]) :=
    universeAvailable.children _ (by simp [InternedProbeProvenance.children])
  have finalBody : Available final.heap (.node b bodyRows 0 [.interned u.identity]) :=
    growth.available _ originalBody
  have substituted := SourceSynthesisUniverseStoredRows.execute_eq_work_of_kernel top u.identity b
    bodyRows targets (.node m [markerRow] 0 []) final finalValid.1 finalBody rfl bodyTop bodyChildren hits
  refine ⟨value, final, done, finalValid, growth, available, prepared, free, ?_⟩
  rw [substituted]
  simp only [InternedNestedConstruction.work, pureNode]

end MicroCFTA.SourceSynthesisUniverseBodySubstitution
