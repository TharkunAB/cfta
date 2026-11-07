import MicroCFTA.SourceSynthesisUniverseMarkerIdentity
import MicroCFTA.SourceSynthesisUniverseMarkerReference

/-!
# Physical results of marker and recursive-reference cross children

The actual D2 lookup and closed-domain reset reach the checked marker/Mu
product. Its physical result is Empty or the original marker. The reverse
request takes one source swap step. Both results retain their full machines.
-/
namespace MicroCFTA.SourceSynthesisUniverseMarkerReferenceIdentity
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (second secondState)
open SourceSynthesisUniverseMarkerReference (second_valid marker_reference marker_universe_reset)

variable {Symbol Guard : Type}

private abbrev muValue (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) : Value Symbol Guard :=
  .mu u (.node b rows 0 [.interned u.identity]) depth ordinary

private abbrev markerValue (m : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth : Nat) : Value Symbol Guard := .node m rows depth []

private abbrev refValue (u : Interned NodeKey) : Value Symbol Guard :=
  .reference (.interned u.identity)

/-- The actual forward cross-child returns Empty or the original cached marker. -/
theorem marker_reference_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)) (markerRow : EdgeValue Symbol Guard)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (top : Guard) (conjoinTop : conjoin top top = top)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (muValue u b bodyRows depth ordinary))
    (markerAvailable : Available state.heap (markerValue m [markerRow] 0))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top) :
    ∃ value final,
      execute emptyGuard conjoin 7 (second u b bodyRows depth ordinary state).1
        (markerValue m [markerRow] 0) (refValue u) (secondState u b bodyRows depth ordinary state) =
        .done value final ∧ Facts final.heap ∧ Available final.heap value ∧ (value = .empty ∨ value = markerValue m [markerRow] 0) := by
  obtain ⟨value, final, done, finalFacts, available, classified⟩ :=
    SourceSynthesisUniverseMarkerIdentity.marker_universe_complete emptyGuard conjoin top conjoinTop
      m b u markerRow bodyRows depth ordinary (secondState u b bodyRows depth ordinary state)
      ⟨facts, second_valid u b bodyRows depth ordinary state valid⟩ markerAvailable universeAvailable leaf markerTop bodyTop
  refine ⟨value, final, ?_, finalFacts, available, classified⟩
  change onNode emptyGuard conjoin (execute emptyGuard conjoin 6)
    (second u b bodyRows depth ordinary state).1 (markerValue m [markerRow] 0) (refValue u)
    (secondState u b bodyRows depth ordinary state) = _
  rw [marker_reference u b m bodyRows [markerRow] 0 depth ordinary emptyGuard conjoin _
    state facts valid universeAvailable markerAvailable]
  change onNode emptyGuard conjoin (execute emptyGuard conjoin 5)
    (second u b bodyRows depth ordinary state).1 (markerValue m [markerRow] 0)
    (muValue u b bodyRows depth ordinary) (secondState u b bodyRows depth ordinary state) = _
  rw [marker_universe_reset u b m bodyRows [markerRow] 0 depth ordinary emptyGuard conjoin _ state valid]
  exact done

/-- The actual reverse cross-child preserves the same physical result classification. -/
theorem reference_marker_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)) (markerRow : EdgeValue Symbol Guard)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (top : Guard) (conjoinTop : conjoin top top = top)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (muValue u b bodyRows depth ordinary))
    (markerAvailable : Available state.heap (markerValue m [markerRow] 0))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top) :
    ∃ value final,
      execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary state).1
        (refValue u) (markerValue m [markerRow] 0) (secondState u b bodyRows depth ordinary state) =
        .done value final ∧ Facts final.heap ∧ Available final.heap value ∧ (value = .empty ∨ value = markerValue m [markerRow] 0) := by
  obtain ⟨value, final, done, finalFacts, available, classified⟩ :=
    marker_reference_complete u b m bodyRows markerRow depth ordinary emptyGuard conjoin top conjoinTop
      state facts valid universeAvailable markerAvailable leaf markerTop bodyTop
  refine ⟨value, final, ?_, finalFacts, available, classified⟩
  have selected : decision (second u b bodyRows depth ordinary state).1.key
      (refValue u) (markerValue m [markerRow] 0) = .swap := by rfl
  change onNode emptyGuard conjoin (execute emptyGuard conjoin 7)
    (second u b bodyRows depth ordinary state).1 (refValue u) (markerValue m [markerRow] 0)
    (secondState u b bodyRows depth ordinary state) = _
  simpa only [onNode, selected] using done

end MicroCFTA.SourceSynthesisUniverseMarkerReferenceIdentity
