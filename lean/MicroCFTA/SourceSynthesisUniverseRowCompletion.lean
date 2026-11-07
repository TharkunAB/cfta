import MicroCFTA.SourceSynthesisUniverseChildCompletion
import MicroCFTA.InternedShallowValues

/-!
# Complete actual universe-body edge requests

The actual zipped child walk carries both cache families through every
ordered child request. Each child is the original marker or Mu reference.
The final edge request uses the complete returned child list. Unequal
arities execute the actual empty-child constructor and retain its effects.
-/
namespace MicroCFTA.SourceSynthesisUniverseRowCompletion
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency InternedBinderProtocol
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceSynthesisUniverseBodyReferenceControl (second secondState)
open InternedStoredClosedMuCompletion (PreparedWithoutMu)

variable {Symbol Guard : Type}

/-- Actual edge execution completes and retains only prepared children with the actual diagonal cutoff name. -/
theorem row_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
    (left right : EdgeValue Symbol Guard)
    (leftKind : ∀ child ∈ left.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned u.identity))
    (rightKind : ∀ child ∈ right.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned u.identity)) :
    ∃ row after,
      edge emptyGuard conjoin (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
        left right before = .done row after ∧ SourceRecursiveIntersectionKernel.Valid after ∧
      Extension before after ∧ EdgeResident after.heap row ∧
      ∀ child ∈ row.children, PreparedWithoutMu child ∧
        ∀ name ∈ child.free, name = .intersection (pair u.identity u.identity).1 (pair u.identity u.identity).2 := by
  let domain := (second u b bodyRows depth ordinary original).1
  let cutoff : Reference := .intersection (pair u.identity u.identity).1 (pair u.identity u.identity).2
  have walkComplete (requests : List (Value Symbol Guard × Value Symbol Guard)) :
      ∀ current : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid current →
        Extension (secondState u b bodyRows depth ordinary original) current →
        (∀ request ∈ requests,
          (request.1 = .node m [markerRow] 0 [] ∨ request.1 = .reference (.interned u.identity)) ∧
          (request.2 = .node m [markerRow] 0 [] ∨ request.2 = .reference (.interned u.identity))) →
        ∃ values after,
          walk (fun request => execute emptyGuard conjoin 8 domain request.1 request.2) requests current =
            .done values after ∧ SourceRecursiveIntersectionKernel.Valid after ∧ Extension current after ∧
          ∀ value ∈ values, Available after.heap value ∧ PreparedWithoutMu value ∧
            ∀ name ∈ value.free, name = cutoff := by
    induction requests with
    | nil =>
        intro current currentValid _ _
        exact ⟨[], current, rfl, currentValid, Extension.refl current, by intro value member; cases member⟩
    | cons request requests ih =>
        intro current currentValid currentGrowth kinds
        have headKind := kinds request List.mem_cons_self
        obtain ⟨value, middle, returned, middleValid, firstGrowth, available, prepared, classified⟩ :=
          SourceSynthesisUniverseChildCompletion.child_complete u b m bodyRows markerRow depth ordinary
            emptyGuard conjoin top conjoinTop original current facts cacheValid universeAvailable markerAvailable
            leaf markerTop bodyTop currentValid currentGrowth request.1 request.2 headKind.1 headKind.2
        have free : ∀ name ∈ value.free, name = cutoff := by
          rcases classified with same | same | same
          · rw [same]
            intro name member
            cases member
          · rw [same]
            intro name member
            cases member
          · rw [same]
            intro name member
            exact List.mem_singleton.mp member
        obtain ⟨values, after, restDone, afterValid, restGrowth, properties⟩ :=
          ih middle middleValid (currentGrowth.trans firstGrowth)
            (fun next member => kinds next (List.mem_cons_of_mem _ member))
        refine ⟨value :: values, after, ?_, afterValid, firstGrowth.trans restGrowth, ?_⟩
        · dsimp only [domain] at restDone ⊢
          simp only [walk, returned, Result.bind, restDone]
        · intro other member
          rcases List.mem_cons.mp member with same | inRest
          · subst other
            exact ⟨restGrowth.available _ available, prepared, free⟩
          · exact properties other inRest
  have makeComplete (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
      (current : Machine Symbol Guard) (currentValid : SourceRecursiveIntersectionKernel.Valid current)
      (earlier : Extension before current)
      (properties : ∀ value ∈ values, Available current.heap value ∧ PreparedWithoutMu value ∧
        ∀ name ∈ value.free, name = cutoff) :
      ∃ row after,
        SourceRecursiveIntersectionKernel.work (makeEdge symbol guard values) current = .done row after ∧
        SourceRecursiveIntersectionKernel.Valid after ∧ Extension before after ∧ EdgeResident after.heap row ∧
        ∀ child ∈ row.children, PreparedWithoutMu child ∧ ∀ name ∈ child.free, name = cutoff := by
    let made := run (makeEdge symbol guard values) current.heap
    let after : Machine Symbol Guard := {current with heap := made.2}
    have available : ∀ value ∈ values, Available current.heap value := fun value member => (properties value member).1
    have checked := work_checked current currentValid (makeEdge symbol guard values) EdgeResident
      (InternedNestedFacts.edge_verified symbol guard values current.heap currentValid.1 available)
    have done : SourceRecursiveIntersectionKernel.work (makeEdge symbol guard values) current =
        .done made.1 after := rfl
    have afterValid : SourceRecursiveIntersectionKernel.Valid after := by
      simpa only [done, Result.state] using checked.valid
    have later : Extension current after := by
      simpa only [done, Result.state] using checked.extension
    have children : made.1.children = values := InternedShallowValues.makeEdge_children symbol guard values
      current.heap currentValid.1.coherent currentValid.1.cached available
    refine ⟨made.1, after, done, afterValid, earlier.trans later, checked.result _ _ done, ?_⟩
    intro child member
    rw [children] at member
    exact (properties child member).2
  by_cases arity : left.children.length = right.children.length
  · obtain ⟨values, middle, walked, middleValid, walkGrowth, properties⟩ :=
      walkComplete (left.children.zip right.children) before beforeValid growth (by
        intro request member
        have inside := List.of_mem_zip member
        exact ⟨leftKind request.1 inside.1, rightKind request.2 inside.2⟩)
    dsimp only [domain] at walked
    obtain ⟨row, after, done, afterValid, extension, resident, children⟩ :=
      makeComplete left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint)
        values middle middleValid walkGrowth properties
    refine ⟨row, after, ?_, afterValid, extension, resident, children⟩
    simpa only [edge, arity, ite_true, walked, Result.bind] using done
  · have properties : ∀ value ∈ ([.empty] : List (Value Symbol Guard)),
        Available before.heap value ∧ PreparedWithoutMu value ∧ ∀ name ∈ value.free, name = cutoff := by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact ⟨empty_available before.heap, .empty, by intro name member; cases member⟩
    obtain ⟨row, after, done, afterValid, extension, resident, children⟩ :=
      makeComplete left.entry.key.symbol emptyGuard [.empty] before beforeValid (Extension.refl before) properties
    refine ⟨row, after, ?_, afterValid, extension, resident, children⟩
    simpa only [edge, arity, ite_false] using done

end MicroCFTA.SourceSynthesisUniverseRowCompletion
