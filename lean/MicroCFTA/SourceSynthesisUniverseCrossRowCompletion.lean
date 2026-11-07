import MicroCFTA.SourceSynthesisUniverseMarkerReference
import MicroCFTA.SourceSynthesisUniverseRowProducts
import MicroCFTA.SourceRecursiveIntersectionKernelStability

/-!
# Actual arrow and catalog cross products

The first child uses the derived marker/reference execution. Both later
children use the entered diagonal cutoff. The edge retains the computed
marker result and the complete machine effects, including constructor work.
This file does not classify the computed marker as a marker or Empty.
-/
namespace MicroCFTA.SourceSynthesisUniverseCrossRowCompletion
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionKernel SourceSynthesisUniverseBodyReferenceControl

section Kernel
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem finish_cross (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (domain : Interned DomainKey) (name : Nat) (left right : EdgeValue Symbol Guard)
    (firstLeft firstRight computed : Value Symbol Guard) (before middle : Machine Symbol Guard)
    (leftChildren : left.children = [firstLeft, .reference (.interned name), .reference (.interned name)])
    (rightChildren : right.children = [firstRight, .reference (.interned name), .reference (.interned name)])
    (seen : pair name name ∈ domain.key.seen)
    (firstDone : execute emptyGuard conjoin 8 domain firstLeft firstRight before = .done computed middle)
    (facts : Facts middle.heap) (available : Available middle.heap computed) :
    edge emptyGuard conjoin (execute emptyGuard conjoin 8 domain) left right before =
      work (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint)
        [computed, repeatedValue (pair name name), repeatedValue (pair name name)]) middle ∧
    let built := InternedConstructorTemplates.run
      (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint)
        [computed, repeatedValue (pair name name), repeatedValue (pair name name)]) middle.heap
    Facts built.2 ∧ EdgeResident built.2 built.1 ∧
      built.1.children = [computed, repeatedValue (pair name name), repeatedValue (pair name name)] ∧
      built.1.entry.key = ⟨left.entry.key.symbol,
        [computed, repeatedValue (pair name name), repeatedValue (pair name name)].map Value.referenceOf,
        conjoin left.entry.key.constraint right.entry.key.constraint⟩ ∧
      ∀ child ∈ built.1.children, Available built.2 child := by
  let cutoff : Value Symbol Guard := repeatedValue (pair name name)
  have later := SourceSynthesisUniverseRowProducts.execute_ref_self
    emptyGuard conjoin 7 domain name middle seen
  have walked : walk (fun children : Value Symbol Guard × Value Symbol Guard =>
      execute emptyGuard conjoin 8 domain children.1 children.2)
      [(firstLeft, firstRight), (.reference (.interned name), .reference (.interned name)),
        (.reference (.interned name), .reference (.interned name))] before =
      .done [computed, cutoff, cutoff] middle := by
    simp only [walk, firstDone, later, Result.bind]
    rfl
  have same : left.children.length = right.children.length := by
    rw [leftChildren, rightChildren]
    rfl
  have zipped : left.children.zip right.children =
      [(firstLeft, firstRight), (.reference (.interned name), .reference (.interned name)),
        (.reference (.interned name), .reference (.interned name))] := by
    rw [leftChildren, rightChildren]
    rfl
  have completed : edge emptyGuard conjoin (execute emptyGuard conjoin 8 domain) left right before =
      work (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint)
        [computed, cutoff, cutoff]) middle := by
    simp only [edge, same, ite_true, zipped, walked, Result.bind]
  have cutoffAvailable : Available middle.heap cutoff := by
    apply reference_available
    intro identity member
    simp [Value.free] at member
  have childrenAvailable : ∀ child ∈ [computed, cutoff, cutoff], Available middle.heap child := by
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact available
    · exact cutoffAvailable
    · exact cutoffAvailable
  have checked := InternedNestedFacts.edge_verified left.entry.key.symbol
    (conjoin left.entry.key.constraint right.entry.key.constraint)
    [computed, cutoff, cutoff] middle.heap facts childrenAvailable
  have readback := InternedShallowValues.makeEdge_children left.entry.key.symbol
    (conjoin left.entry.key.constraint right.entry.key.constraint)
    [computed, cutoff, cutoff] middle.heap facts.coherent facts.cached childrenAvailable
  have key := InternedOrdinaryAbsenceReplay.makeEdge_key left.entry.key.symbol
    (conjoin left.entry.key.constraint right.entry.key.constraint)
    [computed, cutoff, cutoff] middle.heap facts.coherent
  refine ⟨completed, checked.facts, checked.result _ _ rfl, readback, key, ?_⟩
  intro child member
  rw [readback] at member
  exact checked.available child (childrenAvailable child member)

/-- The actual arrow/catalog edge completes with the computed closed marker and two cutoffs. -/
theorem arrow_catalog_complete
    (u b m : Interned NodeKey) (bodyRows markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (markerAvailable : Available state.heap (.node m markerRows markerDepth []))
    (leaves : ∀ row ∈ markerRows, row.children = []) (arrow catalog : EdgeValue Symbol Guard)
    (arrowChildren : arrow.children = [.node m markerRows markerDepth [],
      .reference (.interned u.identity), .reference (.interned u.identity)])
    (catalogChildren : catalog.children = List.replicate 3 (.reference (.interned u.identity))) :
    ∃ computed middle,
      execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary state).1
        (.node m markerRows markerDepth []) (.reference (.interned u.identity))
        (secondState u b bodyRows depth ordinary state) = .done computed middle ∧
      computed.free = [] ∧
      edge emptyGuard conjoin (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary state).1)
        arrow catalog (secondState u b bodyRows depth ordinary state) =
        work (makeEdge arrow.entry.key.symbol (conjoin arrow.entry.key.constraint catalog.entry.key.constraint)
          [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)]) middle ∧
      let built := InternedConstructorTemplates.run
        (makeEdge arrow.entry.key.symbol (conjoin arrow.entry.key.constraint catalog.entry.key.constraint)
          [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)]) middle.heap
      Facts built.2 ∧ EdgeResident built.2 built.1 ∧
        built.1.children = [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)] ∧
        built.1.entry.key = ⟨arrow.entry.key.symbol,
          [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)].map Value.referenceOf,
          conjoin arrow.entry.key.constraint catalog.entry.key.constraint⟩ ∧
        ∀ child ∈ built.1.children, Available built.2 child := by
  obtain ⟨computed, middle, done7, afterFacts, afterAvailable, closed⟩ :=
    SourceSynthesisUniverseMarkerReference.marker_reference_complete
      u b m bodyRows markerRows markerDepth depth ordinary emptyGuard conjoin state facts valid
      universeAvailable markerAvailable leaves
  have complete : NonExhausted (execute emptyGuard conjoin 7
      (second u b bodyRows depth ordinary state).1 (.node m markerRows markerDepth [])
      (.reference (.interned u.identity)) (secondState u b bodyRows depth ordinary state)) := by
    rw [done7]
    trivial
  have done8 := (execute_stable emptyGuard conjoin 7 1 (second u b bodyRows depth ordinary state).1
    (.node m markerRows markerDepth []) (.reference (.interned u.identity))
    (secondState u b bodyRows depth ordinary state) complete).trans done7
  have seen : pair u.identity u.identity ∈ (second u b bodyRows depth ordinary state).1.key.seen :=
    (second_seen u b bodyRows depth ordinary state valid _).mpr (Or.inr rfl)
  refine ⟨computed, middle, done8, closed, ?_⟩
  exact finish_cross emptyGuard conjoin (second u b bodyRows depth ordinary state).1 u.identity arrow catalog
    (.node m markerRows markerDepth []) (.reference (.interned u.identity)) computed
    (secondState u b bodyRows depth ordinary state) middle arrowChildren catalogChildren seen done8 afterFacts afterAvailable

/-- The reverse edge uses the derived eight-level reference/marker execution with its actual effects. -/
theorem catalog_arrow_complete
    (u b m : Interned NodeKey) (bodyRows markerRows : List (EdgeValue Symbol Guard)) (markerDepth : Nat)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (markerAvailable : Available state.heap (.node m markerRows markerDepth []))
    (leaves : ∀ row ∈ markerRows, row.children = []) (catalog arrow : EdgeValue Symbol Guard)
    (catalogChildren : catalog.children = List.replicate 3 (.reference (.interned u.identity)))
    (arrowChildren : arrow.children = [.node m markerRows markerDepth [],
      .reference (.interned u.identity), .reference (.interned u.identity)]) :
    ∃ computed middle,
      execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary state).1
        (.reference (.interned u.identity)) (.node m markerRows markerDepth [])
        (secondState u b bodyRows depth ordinary state) = .done computed middle ∧
      computed.free = [] ∧
      edge emptyGuard conjoin (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary state).1)
        catalog arrow (secondState u b bodyRows depth ordinary state) =
        work (makeEdge catalog.entry.key.symbol (conjoin catalog.entry.key.constraint arrow.entry.key.constraint)
          [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)]) middle ∧
      let built := InternedConstructorTemplates.run
        (makeEdge catalog.entry.key.symbol (conjoin catalog.entry.key.constraint arrow.entry.key.constraint)
          [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)]) middle.heap
      Facts built.2 ∧ EdgeResident built.2 built.1 ∧
        built.1.children = [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)] ∧
        built.1.entry.key = ⟨catalog.entry.key.symbol,
          [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)].map Value.referenceOf,
          conjoin catalog.entry.key.constraint arrow.entry.key.constraint⟩ ∧
        ∀ child ∈ built.1.children, Available built.2 child := by
  obtain ⟨computed, middle, done8, afterFacts, afterAvailable, closed⟩ :=
    SourceSynthesisUniverseMarkerReference.reference_marker_complete
      u b m bodyRows markerRows markerDepth depth ordinary emptyGuard conjoin state facts valid
      universeAvailable markerAvailable leaves
  have seen : pair u.identity u.identity ∈ (second u b bodyRows depth ordinary state).1.key.seen :=
    (second_seen u b bodyRows depth ordinary state valid _).mpr (Or.inr rfl)
  refine ⟨computed, middle, done8, closed, ?_⟩
  exact finish_cross emptyGuard conjoin (second u b bodyRows depth ordinary state).1 u.identity catalog arrow
    (.reference (.interned u.identity)) (.node m markerRows markerDepth []) computed
    (secondState u b bodyRows depth ordinary state) middle catalogChildren arrowChildren seen done8 afterFacts afterAvailable

end Kernel
end MicroCFTA.SourceSynthesisUniverseCrossRowCompletion
