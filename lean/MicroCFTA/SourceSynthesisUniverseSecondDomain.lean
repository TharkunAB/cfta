import MicroCFTA.SourceSynthesisUniverseBodyReferenceControl

/-!
# Complete invariants of the actual second universe domain

The original available Mu supplies its stored body and issued recursive
reference. Two actual Mu entries derive both domain representations and
preserve the constructor heap. Their real domain-cache extensions compose.
The source raw-identity successor wrapper remains in both allocations.
-/
namespace MicroCFTA.SourceSynthesisUniverseSecondDomain
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (first firstState second secondState)

variable {Symbol Guard : Type}

/-- Original Mu provenance derives the valid represented D2 and its complete source-cache extension. -/
theorem second_checked (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard)
    (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (available : Available state.heap (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary)) :
    SourceRecursiveIntersectionKernel.Valid (secondState u b rows depth ordinary state) ∧
      Extension state (secondState u b rows depth ordinary state) ∧
      Domain (secondState u b rows depth ordinary state) (second u b rows depth ordinary state).1 := by
  have bodyAvailable : Available state.heap (.node b rows 0 [.interned u.identity]) :=
    available.children _ (by simp [InternedProbeProvenance.children])
  have referenceAvailable : Available state.heap (.reference (.interned u.identity)) := by
    apply reference_available
    intro identity member
    apply bodyAvailable.issued identity
    simpa only [Value.free] using member
  have firstChecked :
      SourceRecursiveIntersectionKernel.Valid (firstState u b rows depth ordinary state) ∧
      Extension state (firstState u b rows depth ordinary state) ∧
      Domain (firstState u b rows depth ordinary state) (first u b rows depth ordinary state).1 :=
    SourceRecursiveIntersectionKernel.entered state ⟨facts, valid⟩
      IntersectionEmptyDomain.emptyDomain (empty_domain state)
      (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary)
      (.reference (.interned u.identity)) available referenceAvailable u.identity u.identity
  have secondChecked :
      SourceRecursiveIntersectionKernel.Valid (secondState u b rows depth ordinary state) ∧
      Extension (firstState u b rows depth ordinary state) (secondState u b rows depth ordinary state) ∧
      Domain (secondState u b rows depth ordinary state) (second u b rows depth ordinary state).1 :=
    SourceRecursiveIntersectionKernel.entered (firstState u b rows depth ordinary state)
      firstChecked.1 (first u b rows depth ordinary state).1 firstChecked.2.2
      (.node b rows 0 [.interned u.identity])
      (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary)
      bodyAvailable available b.identity u.identity
  exact ⟨secondChecked.1, firstChecked.2.1.trans secondChecked.2.1, secondChecked.2.2⟩

end MicroCFTA.SourceSynthesisUniverseSecondDomain
