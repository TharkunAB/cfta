import MicroCFTA.SourceSynthesisUniverseBodyProductCompletion

/-!
# The unused inner binder of the actual universe-body request

The actual ordinary product returns no free name or the outer diagonal
placeholder. Coherent body and Mu identities make that placeholder distinct
from the inner pair name. The inner optional binder returns the same value
and heap. Both kernel runs retain the complete returned machine.
-/
namespace MicroCFTA.SourceSynthesisUniverseInnerMu
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts InternedStoredClosedMuCompletion
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl

private theorem inner_name_ne_outer (b u : Nat) (different : b ≠ u) :
    Reference.intersection (pair b u).1 (pair b u).2 ≠
      Reference.intersection (pair u u).1 (pair u u).2 := by
  intro same
  have components := Reference.intersection.inj same
  have lower := components.1
  have upper := components.2
  simp only [pair, Nat.min_self, Nat.max_self] at lower upper
  exact different (by omega)

section Kernel
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual body diagonal completes at nine levels with only the possible outer placeholder. -/
theorem execute_body_complete
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
      execute emptyGuard conjoin 9 (second u b bodyRows depth ordinary original).1
        (.node b bodyRows 0 [.interned u.identity]) (.node b bodyRows 0 [.interned u.identity])
        (secondState u b bodyRows depth ordinary original) = .done value final ∧
      Valid final ∧ Extension original final ∧ Available final.heap value ∧ PreparedWithoutMu value ∧
      (value.free = [] ∨ value.free = [.intersection (pair u.identity u.identity).1
        (pair u.identity u.identity).2]) := by
  obtain ⟨value, final, completed, finalValid, growth, available, prepared, free⟩ :=
    SourceSynthesisUniverseBodyProductCompletion.node_complete u b m bodyRows markerRow depth ordinary
      emptyGuard conjoin top conjoinTop original facts cacheValid universeAvailable markerAvailable
      leaf markerTop bodyTop bodyChildren
  refine ⟨value, final, ?_, finalValid, ?_, available, prepared, free⟩
  · change onNode emptyGuard conjoin (execute emptyGuard conjoin 8)
      (second u b bodyRows depth ordinary original).1 (.node b bodyRows 0 [.interned u.identity])
      (.node b bodyRows 0 [.interned u.identity]) (secondState u b bodyRows depth ordinary original) = _
    exact (body_diagonal_onNode u b bodyRows depth ordinary emptyGuard conjoin
      (execute emptyGuard conjoin 8) original facts cacheValid universeAvailable).trans completed
  · exact (SourceSynthesisUniverseSecondDomain.second_checked u b bodyRows depth ordinary original
      facts cacheValid universeAvailable).2.1.trans growth

/-- The actual body/reference request returns that same body without inner-binder effects. -/
theorem execute_body_reference_complete
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
      execute emptyGuard conjoin 9 (second u b bodyRows depth ordinary original).1
        (.node b bodyRows 0 [.interned u.identity]) (.node b bodyRows 0 [.interned u.identity])
        (secondState u b bodyRows depth ordinary original) = .done value final ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu (pair b.identity u.identity) value final.heap =
        .done value final.heap ∧
      execute emptyGuard conjoin 11 (first u b bodyRows depth ordinary original).1
        (.node b bodyRows 0 [.interned u.identity]) (.reference (.interned u.identity))
        (firstState u b bodyRows depth ordinary original) = .done value final ∧
      Valid final ∧ Extension original final ∧ Available final.heap value ∧ PreparedWithoutMu value ∧
      (value.free = [] ∨ value.free = [.intersection (pair u.identity u.identity).1
        (pair u.identity u.identity).2]) := by
  obtain ⟨value, final, done9, finalValid, growth, available, prepared, free⟩ :=
    execute_body_complete u b m bodyRows markerRow depth ordinary emptyGuard conjoin top conjoinTop
      original facts cacheValid universeAvailable markerAvailable leaf markerTop bodyTop bodyChildren
  have different := body_identity_ne u b bodyRows depth ordinary original facts universeAvailable
  have absent : Reference.intersection (pair b.identity u.identity).1
      (pair b.identity u.identity).2 ∉ value.free := by
    intro member
    rcases free with closed | singleton
    · rw [closed] at member
      cases member
    · have same : Reference.intersection (pair b.identity u.identity).1 (pair b.identity u.identity).2 =
          Reference.intersection (pair u.identity u.identity).1 (pair u.identity u.identity).2 := by
        simpa only [singleton, List.mem_singleton] using member
      exact inner_name_ne_outer b.identity u.identity different same
  have unused := SourceRecursiveIntersectionMaybeMu.unused (pair b.identity u.identity) value final.heap absent
  refine ⟨value, final, done9, unused, ?_, finalValid, growth, available, prepared, free⟩
  rw [execute_body_reference u b bodyRows depth ordinary emptyGuard conjoin 9 original facts cacheValid universeAvailable]
  simp only [done9, Result.bind, unused, construction]

end Kernel
end MicroCFTA.SourceSynthesisUniverseInnerMu
