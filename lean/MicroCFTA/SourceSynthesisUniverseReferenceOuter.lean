import MicroCFTA.SourceSynthesisUniverseInnerMu

/-!
# The actual outer continuation of the open universe request

The original empty-domain request swaps the reference and enters Mu.
The actual eleven-level body/reference request completes in the original
first machine. Its returned body supplies the literal outer optional-Mu
construction. This equation retains that construction's exact success or
pending outcome and all returned caches. It does not assert completion
of the outer construction.
-/
namespace MicroCFTA.SourceSynthesisUniverseReferenceOuter
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts InternedStoredClosedMuCompletion
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (first firstState)

variable {Symbol Guard : Type}

/-- The complete actual body determines the exact outer optional-Mu continuation at bound thirteen. -/
theorem execute_reference_outer [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (markerRow : EdgeValue Symbol Guard) (depth ordinary : Value Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (top : Guard)
    (conjoinTop : conjoin top top = top) (original : Machine Symbol Guard)
    (facts : Facts original.heap) (cacheValid : Cache.Valid original.domains)
    (universeAvailable : Available original.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (markerAvailable : Available original.heap (.node m [markerRow] 0 []))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top)
    (bodyChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned u.identity)) :
    ∃ value final,
      execute emptyGuard conjoin 11 (first u b bodyRows depth ordinary original).1
        (.node b bodyRows 0 [.interned u.identity]) (.reference (.interned u.identity))
        (firstState u b bodyRows depth ordinary original) = .done value final ∧
      execute emptyGuard conjoin 13 IntersectionEmptyDomain.emptyDomain
        (.reference (.interned u.identity))
        (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original =
        construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity)
          value final.heap) final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧ Extension original final ∧
      Available final.heap value ∧ PreparedWithoutMu value ∧
      (value.free = [] ∨ value.free = [.intersection (pair u.identity u.identity).1
        (pair u.identity u.identity).2]) := by
  obtain ⟨value, final, _, _, bodyDone, finalValid, growth, available, prepared, free⟩ :=
    SourceSynthesisUniverseInnerMu.execute_body_reference_complete u b m bodyRows markerRow depth ordinary
      emptyGuard conjoin top conjoinTop original facts cacheValid universeAvailable markerAvailable
      leaf markerTop bodyTop bodyChildren
  refine ⟨value, final, bodyDone, ?_, finalValid, growth, available, prepared, free⟩
  rw [SourceSynthesisUniverseReferenceControl.execute_referenceMu u
    (.node b bodyRows 0 [.interned u.identity]) depth ordinary emptyGuard conjoin 11 original]
  change (execute emptyGuard conjoin 11 (first u b bodyRows depth ordinary original).1
    (.node b bodyRows 0 [.interned u.identity]) (.reference (.interned u.identity))
    (firstState u b bodyRows depth ordinary original)).bind
      (fun result after => construction
        (SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity) result after.heap) after) = _
  simp only [bodyDone, Result.bind]

end MicroCFTA.SourceSynthesisUniverseReferenceOuter
