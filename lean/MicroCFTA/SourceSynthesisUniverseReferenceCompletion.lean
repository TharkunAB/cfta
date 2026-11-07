import MicroCFTA.SourceSynthesisUniverseReferenceOuter
import MicroCFTA.SourceRecursiveIntersectionKernelCoverage
import MicroCFTA.SourceRecursiveIntersectionKernelScope

/-!
# Completion of the actual open universe request

The derived body execution preserves incoming payload coverage. Its prepared
result therefore completes the outer optional binder. The actual request
returns at thirteen kernel levels with both cache histories retained.
A cold-built input derives coverage and semantic scope from its construction.
Physical equality of the returned value with the original U remains separate.
-/
namespace MicroCFTA.SourceSynthesisUniverseReferenceCompletion
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedRecordCoherence InternedNestedFacts InternedStoredClosedMuCompletion
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl

variable {Symbol Guard : Type}

private theorem reference_available_of_mu (u b : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : Machine Symbol Guard)
    (available : Available state.heap (.mu u (.node b rows 0 [.interned u.identity]) depth ordinary)) :
    Available state.heap (.reference (.interned u.identity)) := by
  have bodyAvailable : Available state.heap (.node b rows 0 [.interned u.identity]) :=
    available.children _ (by simp [InternedProbeProvenance.children])
  apply reference_available
  intro identity member
  apply bodyAvailable.issued identity
  simpa only [Value.free] using member

section Kernel
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Incoming payload coverage derives completion of the actual thirteen-level request. -/
theorem execute_reference_complete
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
    (covered : Covered [] original.heap) :
    ∃ value final,
      execute emptyGuard conjoin 13 IntersectionEmptyDomain.emptyDomain
        (.reference (.interned u.identity))
        (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original = .done value final ∧
      Valid final ∧ Extension original final ∧ Available final.heap value ∧ Covered [] final.heap := by
  obtain ⟨body, bodyFinal, done9, _, done11, bodyValid, growth, bodyAvailable, prepared, _⟩ :=
    SourceSynthesisUniverseInnerMu.execute_body_reference_complete u b m bodyRows markerRow depth ordinary
      emptyGuard conjoin top conjoinTop original facts cacheValid universeAvailable markerAvailable
      leaf markerTop bodyTop bodyChildren
  have base := SourceSynthesisUniverseSecondDomain.second_checked u b bodyRows depth ordinary original
    facts cacheValid universeAvailable
  have bodyInput : Available original.heap (.node b bodyRows 0 [.interned u.identity]) :=
    universeAvailable.children _ (by simp [InternedProbeProvenance.children])
  have bodyCovered : Covered [] bodyFinal.heap :=
    SourceRecursiveIntersectionKernelCoverage.execute_covered (pending := []) emptyGuard conjoin 9
      (second u b bodyRows depth ordinary original).1 (.node b bodyRows 0 [.interned u.identity])
      (.node b bodyRows 0 [.interned u.identity]) (secondState u b bodyRows depth ordinary original)
      base.1 base.2.2 bodyInput bodyInput covered body bodyFinal done9
  have outer : execute emptyGuard conjoin 13 IntersectionEmptyDomain.emptyDomain
      (.reference (.interned u.identity))
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original =
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu (pair u.identity u.identity) body bodyFinal.heap)
        bodyFinal := by
    obtain ⟨other, after, otherDone, otherOuter, _⟩ :=
      SourceSynthesisUniverseReferenceOuter.execute_reference_outer u b m bodyRows markerRow depth ordinary
        emptyGuard conjoin top conjoinTop original facts cacheValid universeAvailable markerAvailable
        leaf markerTop bodyTop bodyChildren
    have identical : (Result.done body bodyFinal : Result Symbol Guard (Value Symbol Guard)) = .done other after :=
      done11.symm.trans otherDone
    cases identical
    exact otherOuter
  obtain ⟨value, heapAfter, outerDone, afterFacts, afterAvailable, heapGrowth, historyGrowth⟩ :=
    SourceRecursiveIntersectionMaybeMu.complete (pair u.identity u.identity) body bodyFinal.heap
      bodyValid.1 bodyAvailable bodyCovered prepared
  let final : Machine Symbol Guard := {bodyFinal with heap := heapAfter}
  have done13 : execute emptyGuard conjoin 13 IntersectionEmptyDomain.emptyDomain
      (.reference (.interned u.identity))
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original = .done value final := by
    rw [outer]
    simp only [outerDone, construction, final]
  have finalGrowth : Extension bodyFinal final := ⟨heapGrowth, historyGrowth, extends_refl _⟩
  have finalCovered : Covered [] final.heap :=
    SourceRecursiveIntersectionKernelCoverage.execute_covered (pending := []) emptyGuard conjoin 13
      IntersectionEmptyDomain.emptyDomain (.reference (.interned u.identity))
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original
      ⟨facts, cacheValid⟩ (empty_domain original)
      (reference_available_of_mu u b bodyRows depth ordinary original universeAvailable)
      universeAvailable covered value final done13
  exact ⟨value, final, done13, ⟨afterFacts, bodyValid.2⟩, growth.trans finalGrowth, afterAvailable, finalCovered⟩

/-- An actual cold build derives incoming coverage and the closed output without a semantic-heap oracle. -/
theorem execute_reference_complete_of_built
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (markerRow : EdgeValue Symbol Guard) (depth ordinary : Value Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (top : Guard)
    (conjoinTop : conjoin top top = top) (original : Machine Symbol Guard)
    (cacheValid : Cache.Valid original.domains)
    (markerAvailable : Available original.heap (.node m [markerRow] 0 []))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top)
    (bodyChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned u.identity))
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty =
      .done (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original.heap) :
    ∃ value final,
      execute emptyGuard conjoin 13 IntersectionEmptyDomain.emptyDomain
        (.reference (.interned u.identity))
        (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original = .done value final ∧
      Valid final ∧ Extension original final ∧ Available final.heap value ∧ Covered [] final.heap ∧ value.free = [] := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression
    (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original.heap built
  have facts : Facts original.heap := semantic.1.normal.facts
  have checked := InternedFreshOrdinaryFacts.build_verified expression [] empty empty_facts
    (by intro value member; cases member)
  have universeAvailable : Available original.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) := checked.result _ _ built
  have covered := InternedFreshOrdinaryCoverage.closed_covered expression
    (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) original.heap built
  obtain ⟨value, final, done13, finalValid, growth, available, finalCovered⟩ :=
    execute_reference_complete u b m bodyRows markerRow depth ordinary emptyGuard conjoin top conjoinTop original
      facts cacheValid universeAvailable markerAvailable leaf markerTop bodyTop bodyChildren covered
  refine ⟨value, final, done13, finalValid, growth, available, finalCovered, ?_⟩
  exact SourceRecursiveIntersectionScopeCalls.execute_closed emptyGuard conjoin 13
    (.reference (.interned u.identity)) (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary)
    original ⟨facts, cacheValid⟩ (reference_available_of_mu u b bodyRows depth ordinary original universeAvailable)
    universeAvailable semantic value final done13

end Kernel
end MicroCFTA.SourceSynthesisUniverseReferenceCompletion
