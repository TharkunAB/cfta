import MicroCFTA.SourceSynthesisUniverseColdReadback
import MicroCFTA.SourceSynthesisUniverseSecondDomain
import MicroCFTA.SourceSynthesisUniverseTopConjunction
import MicroCFTA.SourceSynthesisUniverseBodySubstitution
import MicroCFTA.SourceRecursiveIntersectionKernelScope

/-!
# Original synthesis inputs derive the exact body substitution

Cold source construction supplies the actual universe and body shape.
The complete body product has the same result as the actual source stored
substitution. Both evaluations retain their full final constructor cache.
This result does not identify the outer Mu with the original universe.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodySubstitutionInput
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisUniverseBodyReferenceControl (second secondState)
open InternedStoredClosedMuCompletion (PreparedWithoutMu)
open SourceRecursiveIntersectionControl (pair repeatedValue)

variable [DecidableEq (EdgeKey String Guard)]

/-- Original library and query inputs derive the actual body product and exact source-substitution replay. -/
theorem typesOf_body_substitution (lib : Library) (query : Query) :
    ∃ entry body depth ordinary heap bodyEntry bodyRows value final,
      let initial : SourceRecursiveIntersectionKernel.Machine String Guard := ⟨heap, Cache.emptyState⟩
      let entered := secondState entry bodyEntry bodyRows depth ordinary initial
      InternedFreshOrdinaryConstruction.build (SourceSynthesisFirstOrderConstruction.typesOf lib query)
        [] empty = .done (.mu entry body depth ordinary) heap ∧
      Facts heap ∧ Available heap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned entry.identity) body ∧
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      SourceRecursiveIntersectionKernel.Valid initial ∧
      SourceRecursiveIntersectionKernel.node top SourceEqualityPCSNativeEdge.conjoin
        (SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 8
          (second entry bodyEntry bodyRows depth ordinary initial).1)
        bodyRows bodyRows entered = .done value final ∧
      SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 9
        (second entry bodyEntry bodyRows depth ordinary initial).1 body body entered = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      SourceRecursiveIntersectionKernel.Extension initial final ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap final.heap ∧ Available final.heap value ∧
      PreparedWithoutMu value ∧
      (value.free = [] ∨ value.free =
        [.intersection (pair entry.identity entry.identity).1 (pair entry.identity entry.identity).2]) ∧
      InternedFreshOrdinaryStoredSubstitution.execute body
        (InternedStoredSubstitutionRebind.replacement (.interned entry.identity)
          (repeatedValue (pair entry.identity entry.identity))) final.heap = .done value final.heap := by
  obtain ⟨entry, body, depth, ordinary, heap, built, facts, universeAvailable, shape, closed⟩ :=
    SourceSynthesisUniverseColdReadback.typesOf_cold_mu lib query
  obtain ⟨bodyEntry, bodyRows, _, bodyEq, _, _⟩ :=
    SourceSynthesisUniverseBodyRowKinds.row_kinds top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) (.interned entry.identity) body shape
  let initial : SourceRecursiveIntersectionKernel.Machine String Guard := ⟨heap, Cache.emptyState⟩
  let entered := secondState entry bodyEntry bodyRows depth ordinary initial
  have universeNodeAvailable : Available initial.heap
      (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    rw [← bodyEq]
    exact universeAvailable
  have shapeNode : SourceSynthesisUniverseBody.Shape top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) (.interned entry.identity)
      (.node bodyEntry bodyRows 0 [.interned entry.identity]) := by
    rw [← bodyEq]
    exact shape
  obtain ⟨enteredValid, enteredExtension, enteredDomain⟩ :=
    SourceSynthesisUniverseSecondDomain.second_checked entry bodyEntry bodyRows depth ordinary initial
      facts Cache.empty_valid universeNodeAvailable
  obtain ⟨value, final, nodeDone, finalValid, growth, available, prepared, free, substitution⟩ :=
    SourceSynthesisUniverseBodySubstitution.node_substitution top
      (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query) entry bodyEntry bodyRows depth ordinary
      top SourceEqualityPCSNativeEdge.conjoin SourceSynthesisUniverseTopConjunction.native_conjoin_top
      initial facts Cache.empty_valid universeNodeAvailable shapeNode
  have actualDone : SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 9
      (second entry bodyEntry bodyRows depth ordinary initial).1 body body entered = .done value final := by
    rw [bodyEq]
    change SourceRecursiveIntersectionKernel.onNode top SourceEqualityPCSNativeEdge.conjoin
      (SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 8)
      (second entry bodyEntry bodyRows depth ordinary initial).1
      (.node bodyEntry bodyRows 0 [.interned entry.identity])
      (.node bodyEntry bodyRows 0 [.interned entry.identity]) entered = .done value final
    rw [SourceSynthesisUniverseBodyReferenceControl.body_diagonal_onNode entry bodyEntry bodyRows depth ordinary
      top SourceEqualityPCSNativeEdge.conjoin _ initial facts Cache.empty_valid universeNodeAvailable]
    exact nodeDone
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed
    (SourceSynthesisFirstOrderConstruction.typesOf lib query) (.mu entry body depth ordinary) heap built
  have bodyAvailable : Available entered.heap body := universeAvailable.children _ (by simp [children])
  have finalSemantic := (SourceRecursiveIntersectionScopeCalls.execute_scoped top SourceEqualityPCSNativeEdge.conjoin 9
    (second entry bodyEntry bodyRows depth ordinary initial).1 body body entered enteredValid enteredDomain
    bodyAvailable bodyAvailable semantic value final actualDone).1
  have sourceReplay : InternedFreshOrdinaryStoredSubstitution.execute body
      (InternedStoredSubstitutionRebind.replacement (.interned entry.identity)
        (repeatedValue (pair entry.identity entry.identity))) final.heap = .done value final.heap := by
    rw [bodyEq]
    exact substitution
  exact ⟨entry, body, depth, ordinary, heap, bodyEntry, bodyRows, value, final, built, facts,
    universeAvailable, shape, bodyEq, closed, ⟨facts, Cache.empty_valid⟩, nodeDone, actualDone,
    finalValid, enteredExtension.trans growth, finalSemantic, available, prepared, free, sourceReplay⟩

end MicroCFTA.SourceSynthesisUniverseBodySubstitutionInput
