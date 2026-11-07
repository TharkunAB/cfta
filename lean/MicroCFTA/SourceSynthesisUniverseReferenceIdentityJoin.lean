import MicroCFTA.SourceSynthesisUniverseReferenceOuter

/-!
# Exact identity at the actual outer universe continuation

The actual body result identifies the derived inner run. The actual outer
optional-Mu result then determines the thirteen-level request. These are
internal execution conditions for the original-input application to derive.
The result retains the complete final heap and domain cache.
-/
namespace MicroCFTA.SourceSynthesisUniverseReferenceIdentityJoin
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (first firstState second secondState)

variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual body and optional-Mu identity runs determine the exact outer result and machine. -/
theorem execute_reference_identity
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
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned u.identity))
    (product : Value Symbol Guard) (final : Machine Symbol Guard)
    (bodyDone : node emptyGuard conjoin
      (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
      bodyRows bodyRows (secondState u b bodyRows depth ordinary original) = .done product final)
    (outerDone : SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity) product final.heap =
      .done (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) final.heap) :
    execute emptyGuard conjoin 13 IntersectionEmptyDomain.emptyDomain
      (.reference (.interned u.identity))
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original =
        .done (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) final := by
  have actual9 : execute emptyGuard conjoin 9 (second u b bodyRows depth ordinary original).1
      (.node b bodyRows 0 [.interned u.identity]) (.node b bodyRows 0 [.interned u.identity])
      (secondState u b bodyRows depth ordinary original) = .done product final := by
    change onNode emptyGuard conjoin (execute emptyGuard conjoin 8)
      (second u b bodyRows depth ordinary original).1 (.node b bodyRows 0 [.interned u.identity])
      (.node b bodyRows 0 [.interned u.identity]) (secondState u b bodyRows depth ordinary original) = _
    exact (SourceSynthesisUniverseBodyReferenceControl.body_diagonal_onNode u b bodyRows depth ordinary
      emptyGuard conjoin (execute emptyGuard conjoin 8) original facts cacheValid universeAvailable).trans bodyDone
  obtain ⟨inner, innerFinal, done9, _innerMu, done11, _valid, _growth, _available, _prepared, _free⟩ :=
    SourceSynthesisUniverseInnerMu.execute_body_reference_complete u b m bodyRows markerRow depth ordinary
      emptyGuard conjoin top conjoinTop original facts cacheValid universeAvailable markerAvailable
      leaf markerTop bodyTop bodyChildren
  have actual11 : execute emptyGuard conjoin 11 (first u b bodyRows depth ordinary original).1
      (.node b bodyRows 0 [.interned u.identity]) (.reference (.interned u.identity))
      (firstState u b bodyRows depth ordinary original) = .done product final :=
    done11.trans (done9.symm.trans actual9)
  obtain ⟨other, after, otherDone, outer, _remaining⟩ :=
    SourceSynthesisUniverseReferenceOuter.execute_reference_outer u b m bodyRows markerRow depth ordinary
      emptyGuard conjoin top conjoinTop original facts cacheValid universeAvailable markerAvailable
      leaf markerTop bodyTop bodyChildren
  have same := Result.done.inj (actual11.symm.trans otherDone)
  rw [← same.1, ← same.2] at outer
  rw [outer]
  simp only [outerDone, construction]

end MicroCFTA.SourceSynthesisUniverseReferenceIdentityJoin
