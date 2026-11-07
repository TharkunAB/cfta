import MicroCFTA.SourceSynthesisUniverseCrossRowCompletion
import MicroCFTA.SourceSynthesisUniverseMarkerReferenceIdentity

/-!
# Physical identity of the actual arrow and catalog cross rows

The classified marker execution and the completed edge execution identify
the same child and machine. Empty makes the edge dead. The original marker
gives the literal arrow-self children and top constraint. All constructor
and domain-cache effects remain in the actual returned machine.
-/
namespace MicroCFTA.SourceSynthesisUniverseCrossRowIdentity
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceRecursiveIntersectionKernel SourceSynthesisUniverseBodyReferenceControl
open EqualityLeafProjectionPhysical (dead)

variable {Symbol Guard : Type}

private theorem classify_edge (m : Interned NodeKey) (markerRow : EdgeValue Symbol Guard) (name : Nat)
    (top : Guard) (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (symbol : Symbol) (left right result : EdgeValue Symbol Guard) (computed : Value Symbol Guard)
    (leftSymbol : left.entry.key.symbol = symbol)
    (leftTop : left.entry.key.constraint = top) (rightTop : right.entry.key.constraint = top)
    (children : result.children = [computed, repeatedValue (pair name name), repeatedValue (pair name name)])
    (key : result.entry.key = ⟨left.entry.key.symbol,
      [computed, repeatedValue (pair name name), repeatedValue (pair name name)].map Value.referenceOf,
      conjoin left.entry.key.constraint right.entry.key.constraint⟩)
    (classified : computed = .empty ∨ computed = .node m [markerRow] 0 []) :
    dead result = true ∨
      (result.children = [.node m [markerRow] 0 [], repeatedValue (pair name name), repeatedValue (pair name name)] ∧
      result.entry.key = ⟨symbol,
        [.node m [markerRow] 0 [], repeatedValue (pair name name), repeatedValue (pair name name)].map Value.referenceOf,
        top⟩ ∧ dead result = false) := by
  have normalized : result.entry.key = ⟨symbol,
      [computed, repeatedValue (pair name name), repeatedValue (pair name name)].map Value.referenceOf, top⟩ := by
    simpa only [leftSymbol, leftTop, rightTop, conjoinTop] using key
  rcases classified with empty | marker
  · left
    change result.children.any (fun child => child.referenceOf == .empty) = true
    rw [children, empty]
    rfl
  · right
    refine ⟨?_, ?_, ?_⟩
    · simpa only [marker] using children
    · simpa only [marker] using normalized
    · change result.children.any (fun child => child.referenceOf == .empty) = false
      rw [children, marker]
      rfl

section Kernel
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The forward cross edge is dead or has the exact arrow-self key and children. -/
theorem arrow_catalog_identity
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)) (markerRow : EdgeValue Symbol Guard)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (top : Guard) (conjoinTop : conjoin top top = top)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (markerAvailable : Available state.heap (.node m [markerRow] 0 []))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top)
    (arrow catalog : EdgeValue Symbol Guard)
    (arrowChildren : arrow.children = [.node m [markerRow] 0 [],
      .reference (.interned u.identity), .reference (.interned u.identity)])
    (catalogChildren : catalog.children = List.replicate 3 (.reference (.interned u.identity)))
    (arrowTop : arrow.entry.key.constraint = top) (catalogTop : catalog.entry.key.constraint = top) :
    ∃ row final,
      edge emptyGuard conjoin (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary state).1)
        arrow catalog (secondState u b bodyRows depth ordinary state) = .done row final ∧
      Facts final.heap ∧ EdgeResident final.heap row ∧
      (dead row = true ∨
        (row.children = [.node m [markerRow] 0 [], repeatedValue (pair u.identity u.identity),
            repeatedValue (pair u.identity u.identity)] ∧
        row.entry.key = ⟨arrow.entry.key.symbol,
          [.node m [markerRow] 0 [], repeatedValue (pair u.identity u.identity),
            repeatedValue (pair u.identity u.identity)].map Value.referenceOf, top⟩ ∧ dead row = false)) ∧
      ∀ child ∈ row.children, Available final.heap child := by
  have leaves : ∀ row ∈ [markerRow], row.children = [] := by
    intro row member
    simpa only [List.mem_singleton.mp member] using leaf
  obtain ⟨computed, middle, firstDone, _closed, edgeDone, finalFacts, resident, children, key, available⟩ :=
    SourceSynthesisUniverseCrossRowCompletion.arrow_catalog_complete
      u b m bodyRows [markerRow] 0 depth ordinary emptyGuard conjoin state facts valid
      universeAvailable markerAvailable leaves arrow catalog arrowChildren catalogChildren
  obtain ⟨value, after, classifiedDone7, _, _, classified⟩ :=
    SourceSynthesisUniverseMarkerReferenceIdentity.marker_reference_complete
      u b m bodyRows markerRow depth ordinary emptyGuard conjoin top conjoinTop state facts valid
      universeAvailable markerAvailable leaf markerTop bodyTop
  have complete : NonExhausted (execute emptyGuard conjoin 7
      (second u b bodyRows depth ordinary state).1 (.node m [markerRow] 0 [])
      (.reference (.interned u.identity)) (secondState u b bodyRows depth ordinary state)) := by
    rw [classifiedDone7]
    trivial
  have classifiedDone8 := (execute_stable emptyGuard conjoin 7 1
    (second u b bodyRows depth ordinary state).1 (.node m [markerRow] 0 []) (.reference (.interned u.identity))
    (secondState u b bodyRows depth ordinary state) complete).trans classifiedDone7
  have identical : (Result.done value after : Result Symbol Guard (Value Symbol Guard)) = .done computed middle :=
    classifiedDone8.symm.trans firstDone
  have physical : computed = .empty ∨ computed = .node m [markerRow] 0 [] := by
    cases identical
    exact classified
  let built := InternedConstructorTemplates.run
    (makeEdge arrow.entry.key.symbol (conjoin arrow.entry.key.constraint catalog.entry.key.constraint)
      [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)]) middle.heap
  refine ⟨built.1, {middle with heap := built.2}, ?_, finalFacts, resident, ?_, available⟩
  · rw [edgeDone]
    rfl
  · exact classify_edge m markerRow u.identity top conjoin conjoinTop arrow.entry.key.symbol
      arrow catalog built.1 computed rfl arrowTop catalogTop children key physical

/-- The reverse cross edge has the same physical alternatives when the source symbols match. -/
theorem catalog_arrow_identity
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)) (markerRow : EdgeValue Symbol Guard)
    (depth ordinary : Value Symbol Guard) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (top : Guard) (conjoinTop : conjoin top top = top)
    (state : Machine Symbol Guard) (facts : Facts state.heap) (valid : Cache.Valid state.domains)
    (universeAvailable : Available state.heap (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (markerAvailable : Available state.heap (.node m [markerRow] 0 []))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top)
    (catalog arrow : EdgeValue Symbol Guard)
    (catalogChildren : catalog.children = List.replicate 3 (.reference (.interned u.identity)))
    (arrowChildren : arrow.children = [.node m [markerRow] 0 [],
      .reference (.interned u.identity), .reference (.interned u.identity)])
    (sameSymbol : catalog.entry.key.symbol = arrow.entry.key.symbol)
    (catalogTop : catalog.entry.key.constraint = top) (arrowTop : arrow.entry.key.constraint = top) :
    ∃ row final,
      edge emptyGuard conjoin (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary state).1)
        catalog arrow (secondState u b bodyRows depth ordinary state) = .done row final ∧
      Facts final.heap ∧ EdgeResident final.heap row ∧
      (dead row = true ∨
        (row.children = [.node m [markerRow] 0 [], repeatedValue (pair u.identity u.identity),
            repeatedValue (pair u.identity u.identity)] ∧
        row.entry.key = ⟨arrow.entry.key.symbol,
          [.node m [markerRow] 0 [], repeatedValue (pair u.identity u.identity),
            repeatedValue (pair u.identity u.identity)].map Value.referenceOf, top⟩ ∧ dead row = false)) ∧
      ∀ child ∈ row.children, Available final.heap child := by
  have leaves : ∀ row ∈ [markerRow], row.children = [] := by
    intro row member
    simpa only [List.mem_singleton.mp member] using leaf
  obtain ⟨computed, middle, firstDone, _closed, edgeDone, finalFacts, resident, children, key, available⟩ :=
    SourceSynthesisUniverseCrossRowCompletion.catalog_arrow_complete
      u b m bodyRows [markerRow] 0 depth ordinary emptyGuard conjoin state facts valid
      universeAvailable markerAvailable leaves catalog arrow catalogChildren arrowChildren
  obtain ⟨value, after, classifiedDone8, _, _, classified⟩ :=
    SourceSynthesisUniverseMarkerReferenceIdentity.reference_marker_complete
      u b m bodyRows markerRow depth ordinary emptyGuard conjoin top conjoinTop state facts valid
      universeAvailable markerAvailable leaf markerTop bodyTop
  have identical : (Result.done value after : Result Symbol Guard (Value Symbol Guard)) = .done computed middle :=
    classifiedDone8.symm.trans firstDone
  have physical : computed = .empty ∨ computed = .node m [markerRow] 0 [] := by
    cases identical
    exact classified
  let built := InternedConstructorTemplates.run
    (makeEdge catalog.entry.key.symbol (conjoin catalog.entry.key.constraint arrow.entry.key.constraint)
      [computed, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)]) middle.heap
  refine ⟨built.1, {middle with heap := built.2}, ?_, finalFacts, resident, ?_, available⟩
  · rw [edgeDone]
    rfl
  · exact classify_edge m markerRow u.identity top conjoin conjoinTop arrow.entry.key.symbol
      catalog arrow built.1 computed sameSymbol catalogTop arrowTop children key physical

end Kernel
end MicroCFTA.SourceSynthesisUniverseCrossRowIdentity
