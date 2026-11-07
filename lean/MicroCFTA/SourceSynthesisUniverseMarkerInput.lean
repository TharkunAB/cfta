import MicroCFTA.SourceSynthesisUniverseColdReadback
import MicroCFTA.SourceSynthesisUniverseMarkerCompletion
import MicroCFTA.SourceEqualityPCSNativeEdge

/-!
# Original synthesis inputs supply the actual marker/universe calculation

Original Library and Query data construct the recursive type universe from
empty caches. Its distinguished live arrow retains the marker child through
canonical edge ordering. This supplies the marker's actual availability.
The source kernel then completes marker/universe intersection at bound five.
The result retains both physical caches. This theorem does not classify the
result as the marker or EmptyNode from catalog membership.
-/
namespace MicroCFTA.SourceSynthesisUniverseMarkerInput
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax

section Generic
variable {Symbol Guard : Type}

/-- A live first row survives canonical ordering without any condition on later rows. -/
theorem live_head_retained (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (live : first.children.any (fun child => child.referenceOf == .empty) = false) :
    first ∈ canonicalEdges (surviving (first :: rest)) := by
  have kept : surviving (first :: rest) = first :: surviving rest := by simp [surviving, live]
  rw [kept]
  unfold canonicalEdges
  apply List.mem_filterMap.mpr
  refine ⟨first.entry.identity, ?_, ?_⟩
  · apply (EnumerationBuilderCaches.canonicalIds_member _ _).mpr
    exact List.mem_map.mpr ⟨first, List.mem_cons_self, rfl⟩
  · simp

/-- Actual body shape and Mu availability supply its retained closed nullary marker. -/
theorem shape_marker_available (top : Guard) (catalog : List (String × Nat))
    (entry : Interned NodeKey) (body depth ordinary : Value String Guard)
    (heap : InternedConstructorTemplates.State String Guard)
    (universeAvailable : Available heap (.mu entry body depth ordinary))
    (shape : SourceSynthesisUniverseBody.Shape top catalog (.interned entry.identity) body) :
    ∃ bodyEntry bodyRows markerEntry markerEdge marker,
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      marker = .node markerEntry [markerEdge] 0 [] ∧
      SourceSynthesisUniverseBody.RowReadback "(->)" top [] marker ∧
      markerEdge.children = [] ∧ marker ∈ children body ∧ Available heap marker := by
  obtain ⟨bodyEntry, marker, arrow, rest, bodyEq, markerRead, arrowChildren, _, _⟩ := shape
  have markerReadback := markerRead
  obtain ⟨markerEntry, markerEdge, markerEq, markerChildren, _⟩ := markerRead
  have markerNode : marker = .node markerEntry [markerEdge] 0 [] := by
    simpa [maximumDepth, childFree, canonicalFree] using markerEq
  have live : arrow.children.any (fun child => child.referenceOf == .empty) = false := by
    simp [arrowChildren, markerNode, Value.referenceOf]
  have retained := live_head_retained arrow rest live
  have member : marker ∈ children body := by
    rw [bodyEq]
    apply List.mem_flatMap.mpr
    exact ⟨arrow, retained, by simp [arrowChildren]⟩
  have bodyAvailable : Available heap body := universeAvailable.children body (by simp [children])
  exact ⟨bodyEntry, _, markerEntry, markerEdge, marker, bodyEq, markerNode, markerReadback,
    markerChildren, member, bodyAvailable.children marker member⟩

end Generic

open SourceSynthesisGeneralizeSyntax (Guard top)
variable [DecidableEq (EdgeKey String Guard)]

/-- Original inputs derive the constructed universe, its actual marker, and the completed source request. -/
theorem typesOf_marker_complete (lib : Library) (query : Query) :
    ∃ entry body depth ordinary heap marker value final,
      InternedFreshOrdinaryConstruction.build (SourceSynthesisFirstOrderConstruction.typesOf lib query)
        [] empty = .done (.mu entry body depth ordinary) heap ∧
      Facts heap ∧ Available heap (.mu entry body depth ordinary) ∧
      SourceSynthesisUniverseBody.Shape top (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
        (.interned entry.identity) body ∧
      (Value.mu entry body depth ordinary).free = [] ∧
      SourceSynthesisUniverseBody.RowReadback "(->)" top [] marker ∧
      marker ∈ children body ∧ Available heap marker ∧
      SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 5
        IntersectionEmptyDomain.emptyDomain marker (.mu entry body depth ordinary)
        ⟨heap, Cache.emptyState⟩ = .done value final ∧
      Facts final.heap ∧ Available final.heap value ∧ value.free = [] := by
  obtain ⟨entry, body, depth, ordinary, heap, built, facts, universeAvailable, shape, closed⟩ :=
    SourceSynthesisUniverseColdReadback.typesOf_cold_mu lib query
  obtain ⟨bodyEntry, bodyRows, markerEntry, markerEdge, marker, bodyEq, markerEq,
      markerRead, markerChildren, member, markerAvailable⟩ :=
    shape_marker_available top (SourceSynthesisFirstOrderConstruction.constructorCatalog lib query)
      entry body depth ordinary heap universeAvailable shape
  let initial : SourceRecursiveIntersectionKernel.Machine String Guard := ⟨heap, Cache.emptyState⟩
  have initialValid : SourceRecursiveIntersectionKernel.Valid initial := ⟨facts, Cache.empty_valid⟩
  have markerNodeAvailable : Available initial.heap (.node markerEntry [markerEdge] 0 []) := by
    rw [← markerEq]
    exact markerAvailable
  have universeNodeAvailable : Available initial.heap
      (.mu entry (.node bodyEntry bodyRows 0 [.interned entry.identity]) depth ordinary) := by
    rw [← bodyEq]
    exact universeAvailable
  obtain ⟨value, final, done, finalFacts, available, resultClosed⟩ :=
    SourceSynthesisUniverseMarkerCompletion.marker_universe_complete top SourceEqualityPCSNativeEdge.conjoin
      markerEntry bodyEntry entry [markerEdge] bodyRows 0 depth ordinary initial initialValid
      markerNodeAvailable universeNodeAvailable (by
        intro row included
        have same := List.mem_singleton.mp included
        subst row
        exact markerChildren)
  have actualDone : SourceRecursiveIntersectionKernel.execute top SourceEqualityPCSNativeEdge.conjoin 5
      IntersectionEmptyDomain.emptyDomain marker (.mu entry body depth ordinary) initial = .done value final := by
    rw [markerEq, bodyEq]
    exact done
  exact ⟨entry, body, depth, ordinary, heap, marker, value, final, built, facts, universeAvailable,
    shape, closed, markerRead, member, markerAvailable, actualDone, finalFacts, available, resultClosed⟩

end MicroCFTA.SourceSynthesisUniverseMarkerInput
