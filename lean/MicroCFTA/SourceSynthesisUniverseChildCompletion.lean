import MicroCFTA.SourceSynthesisUniverseSecondDomain
import MicroCFTA.SourceSynthesisUniverseMarkerReferenceIdentity
import MicroCFTA.SourceSynthesisUniverseDomainReplay
import MicroCFTA.SourceSynthesisUniverseRowProducts
import MicroCFTA.SourceRecursiveIntersectionKernelVerified
import MicroCFTA.SourceRecursiveIntersectionKernelStability

/-!
# Uniform child completion after earlier universe-product siblings

Every actual body child is the closed marker or the original Mu reference.
The four ordered child pairs complete at bound eight. Earlier actual source
extensions preserve the original second domain and its binding. Both real
domain allocations replay at the later machine. Completed execution derives
the next machine invariants and preserves every preceding cache effect.
-/
namespace MicroCFTA.SourceSynthesisUniverseChildCompletion
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceSynthesisUniverseBodyReferenceControl (second secondState second_seen)
open InternedStoredClosedMuCompletion (PreparedWithoutMu)

variable {Symbol Guard : Type}

/-- Every literal marker/reference child pair completes after any preceding actual sibling extension. -/
theorem child_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (markerRow : EdgeValue Symbol Guard) (depth ordinary : Value Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (top : Guard)
    (conjoinTop : conjoin top top = top) (original before : Machine Symbol Guard)
    (facts : Facts original.heap) (cacheValid : Cache.Valid original.domains)
    (universeAvailable : Available original.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (markerAvailable : Available original.heap (.node m [markerRow] 0 []))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top)
    (beforeValid : SourceRecursiveIntersectionKernel.Valid before)
    (growth : Extension (secondState u b bodyRows depth ordinary original) before)
    (left right : Value Symbol Guard)
    (leftKind : left = .node m [markerRow] 0 [] ∨ left = .reference (.interned u.identity))
    (rightKind : right = .node m [markerRow] 0 [] ∨ right = .reference (.interned u.identity)) :
    ∃ value after,
      execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1 left right before =
        .done value after ∧ SourceRecursiveIntersectionKernel.Valid after ∧ Extension before after ∧
      Available after.heap value ∧ PreparedWithoutMu value ∧
      (value = .empty ∨ value = .node m [markerRow] 0 [] ∨
        value = repeatedValue (pair u.identity u.identity)) := by
  let marker : Value Symbol Guard := .node m [markerRow] 0 []
  let recursive : Value Symbol Guard := .reference (.interned u.identity)
  let cutoff : Value Symbol Guard := repeatedValue (pair u.identity u.identity)
  let domain := (second u b bodyRows depth ordinary original).1
  have originalDomain := SourceSynthesisUniverseSecondDomain.second_checked u b bodyRows depth ordinary
    original facts cacheValid universeAvailable
  have known : Domain before domain := Domain.grows domain originalDomain.2.2 growth
  have bodyAvailable : Available original.heap (.node b bodyRows 0 [.interned u.identity]) :=
    universeAvailable.children _ (by simp [InternedProbeProvenance.children])
  have referenceAvailable : Available original.heap recursive := by
    apply reference_available
    intro identity member
    apply bodyAvailable.issued identity
    simpa only [Value.free] using member
  have universeBefore : Available before.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) :=
    growth.available _ universeAvailable
  have markerBefore : Available before.heap marker := growth.available _ markerAvailable
  have referenceBefore : Available before.heap recursive := growth.available _ referenceAvailable
  have leftAvailable : Available before.heap left := by
    rcases leftKind with rfl | rfl
    · exact markerBefore
    · exact referenceBefore
  have rightAvailable : Available before.heap right := by
    rcases rightKind with rfl | rfl
    · exact markerBefore
    · exact referenceBefore
  have sameDomain : (second u b bodyRows depth ordinary before).1 = domain := by
    have replay := SourceSynthesisUniverseDomainReplay.second_replay u b bodyRows depth ordinary
      original before cacheValid growth
    have projected := congrArg
      (fun result : Interned IntersectionFlatMemoKeyDomain.DomainKey ×
          Cache.State IntersectionFlatMemoKeyDomain.DomainKey => result.1) replay
    exact projected
  have sameState : secondState u b bodyRows depth ordinary before = before :=
    SourceSynthesisUniverseDomainReplay.secondState_replay u b bodyRows depth ordinary
      original before cacheValid growth
  have completed : ∃ value after,
      execute emptyGuard conjoin 8 domain left right before = .done value after ∧
      (value = .empty ∨ value = marker ∨ value = cutoff) := by
    rcases leftKind with rfl | rfl
    · rcases rightKind with rfl | rfl
      · exact ⟨marker, before,
          SourceSynthesisUniverseRowProducts.execute_marker_self emptyGuard conjoin 6 domain
            m [markerRow] 0 before, Or.inr (Or.inl rfl)⟩
      · obtain ⟨value, after, done, _, _, classified⟩ :=
          SourceSynthesisUniverseMarkerReferenceIdentity.marker_reference_complete u b m bodyRows markerRow
            depth ordinary emptyGuard conjoin top conjoinTop before beforeValid.1 beforeValid.2
            universeBefore markerBefore leaf markerTop bodyTop
        rw [sameState, sameDomain] at done
        have stable := execute_stable emptyGuard conjoin 7 1 domain marker recursive before
          (by rw [done]; trivial)
        exact ⟨value, after, stable.trans done,
          classified.elim Or.inl (fun same => Or.inr (Or.inl same))⟩
    · rcases rightKind with rfl | rfl
      · obtain ⟨value, after, done, _, _, classified⟩ :=
          SourceSynthesisUniverseMarkerReferenceIdentity.reference_marker_complete u b m bodyRows markerRow
            depth ordinary emptyGuard conjoin top conjoinTop before beforeValid.1 beforeValid.2
            universeBefore markerBefore leaf markerTop bodyTop
        rw [sameState, sameDomain] at done
        exact ⟨value, after, done, classified.elim Or.inl (fun same => Or.inr (Or.inl same))⟩
      · have seen : pair u.identity u.identity ∈ domain.key.seen :=
          (second_seen u b bodyRows depth ordinary original cacheValid _).mpr (Or.inr rfl)
        exact ⟨cutoff, before,
          SourceSynthesisUniverseRowProducts.execute_ref_self emptyGuard conjoin 7 domain u.identity before seen,
          Or.inr (Or.inr rfl)⟩
  obtain ⟨value, after, done, classified⟩ := completed
  have checked := execute_checked emptyGuard conjoin 8 domain left right before beforeValid known
    leftAvailable rightAvailable
  have prepared : PreparedWithoutMu value := by
    rcases classified with same | same | same
    · rw [same]
      exact .empty
    · rw [same]
      exact .closed _ rfl
    · rw [same]
      exact .reference _
  refine ⟨value, after, done, ?_, ?_, checked.result value after done, prepared, classified⟩
  · simpa only [done, Result.state] using checked.valid
  · simpa only [done, Result.state] using checked.extension

end MicroCFTA.SourceSynthesisUniverseChildCompletion
