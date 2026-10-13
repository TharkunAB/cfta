import MicroCFTA.MergedAdaptiveColumns

/-!
# Actual edge construction after adaptive child calls

The recursive action runs in the cache returned by the preceding child.
Both source group branches then intern the edge with the complete returned
children. No state-independent child computation is assumed.
-/
namespace MicroCFTA.MergedAdaptiveEdges
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnion
open MergedPhysicalGroupCalls MergedPhysicalGroupEdges MergedOrdinaryHeight
open MergedAdaptiveEffects Language

/-- A completed physical edge includes all original row languages in its final cache. -/
structure EdgeResult [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (inputs : List (EdgeValue Symbol Guard)) (edge : EdgeValue Symbol Guard) : Prop where
  extension : Extension before after outputs
  resident : EdgeResident after edge
  covers : ∀ original ∈ inputs, ∀ term, EdgeAccepts before meaning original term → EdgeAccepts after meaning edge term

/-- Run the small source branch with child calls at their actual states. -/
def small [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (edge : EdgeValue Symbol Guard) : Action Symbol Guard (EdgeValue Symbol Guard) :=
  MergedAdaptiveEffects.bind (MergedAdaptiveEffects.map recurse edge.children) fun values =>
    work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)

/-- The adaptive small branch preserves the original edge language. -/
theorem small_complete [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Context state outputs → Available state value →
      ∃ result after, recurse value state = some (result, after) ∧ Result state after outputs meaning [value] result)
    (edge : EdgeValue Symbol Guard) (bounded : ∀ value ∈ edge.children, height value ≤ limit)
    (state : State Symbol Guard) (context : Context state outputs) (resident : EdgeResident state edge) :
    ∃ result after, small recurse edge state = some (result, after) ∧ EdgeResult state after outputs meaning [edge] result := by
  obtain ⟨children, middle, childrenDone, extension, available, covers⟩ :=
    map_complete recurse (fun value => [value]) edge.children outputs meaning
      (fun value member state context inputs => smaller value (bounded value member) state context (inputs value List.mem_cons_self))
      state context (fun value member child included => by
        rw [List.mem_singleton.mp included]
        exact context.facts.cached.edges edge.entry.key edge resident value member)
  let result := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint children) middle
  have built := extension.context.makeEdge middle outputs edge.entry.key.symbol edge.entry.key.constraint children available
  have fields := makeEdge_fields middle extension.context.facts edge.entry.key.symbol edge.entry.key.constraint children available
  have finalExtension := Extension.work (makeEdge edge.entry.key.symbol edge.entry.key.constraint children) middle outputs extension.context built.1
  refine ⟨result.1, result.2, ?_, ⟨extension.trans finalExtension, built.2, ?_⟩⟩
  · simp only [small, MergedAdaptiveEffects.bind, childrenDone, Option.bind_some, work]; rfl
  · intro original member term accepted
    have sameOriginal := List.mem_singleton.mp member
    subst original
    obtain ⟨terms, same, runs, guard⟩ := accepted
    refine ⟨terms, by rw [fields.1]; exact same, ?_, by rw [fields.2.1]; exact guard⟩
    rw [fields.2.2]
    apply runs_grow middle result.2 outputs extension.context finalExtension.growth meaning children available terms
    apply covers_runs state middle meaning (fun value => [value]) edge.children children terms covers
    exact runs.imp (fun value term accepted => ⟨value, List.mem_cons_self, accepted⟩)

noncomputable section
local instance : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _

/-- Run all current-state column actions and then the unconstrained source edge constructor. -/
def large [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) : Action Symbol Guard (EdgeValue Symbol Guard) :=
  MergedAdaptiveEffects.bind
    (MergedAdaptiveEffects.map (MergedAdaptiveColumns.column recurse outputs meaning unconstrained)
      (MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length))
    fun children => work (makeEdge first.entry.key.symbol top children)

/-- The adaptive large branch includes every original row after actual column and edge effects. -/
theorem large_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (unconstrained : Edge (Value Symbol Guard) Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Context state outputs → Available state value →
      ∃ result after, recurse value state = some (result, after) ∧ Result state after outputs meaning [value] result)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (closed : ∀ edge ∈ first :: rest, ∀ value ∈ edge.children, value.free = [])
    (bounded : ∀ edge ∈ first :: rest, ∀ value ∈ edge.children, height value ≤ limit)
    (keys : SameKey (first :: rest)) (state : State Symbol Guard) (context : Context state outputs)
    (resident : Edges state (first :: rest)) :
    ∃ result after, large recurse outputs meaning unconstrained top first rest state = some (result, after) ∧
      EdgeResult state after outputs meaning (first :: rest) result := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  obtain ⟨children, middle, childrenDone, extension, available, covers⟩ :=
    map_complete (MergedAdaptiveColumns.column recurse outputs meaning unconstrained) id columns outputs meaning
      (fun column member state context inputs => MergedAdaptiveColumns.column_complete recurse limit outputs meaning unconstrained clear smaller
        column state context inputs
        (fun value included => by obtain ⟨edge, outer, inner⟩ := original column member value included; exact closed edge outer value inner)
        (fun value included => by obtain ⟨edge, outer, inner⟩ := original column member value included; exact bounded edge outer value inner))
      state context (fun column member value included => by
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact context.facts.cached.edges edge.entry.key edge (resident edge outer) value inner)
  let result := run (makeEdge first.entry.key.symbol top children) middle
  have built := extension.context.makeEdge middle outputs first.entry.key.symbol top children available
  have fields := makeEdge_fields middle extension.context.facts first.entry.key.symbol top children available
  have finalExtension := Extension.work (makeEdge first.entry.key.symbol top children) middle outputs extension.context built.1
  refine ⟨result.1, result.2, ?_, ⟨extension.trans finalExtension, built.2, ?_⟩⟩
  · dsimp only [columns] at childrenDone
    simp only [large, MergedAdaptiveEffects.bind, childrenDone, Option.bind_some, work]; rfl
  · intro edge member term accepted
    obtain ⟨terms, same, runs, _⟩ := accepted
    obtain ⟨symbol, arity⟩ := keys edge member first List.mem_cons_self
    refine ⟨terms, by rw [fields.1, ← symbol]; exact same, ?_, by rw [fields.2.1]; exact topTrue term⟩
    rw [fields.2.2]
    apply runs_grow middle result.2 outputs extension.context finalExtension.growth meaning children available terms
    apply covers_runs state middle meaning id columns children terms covers
    have columnRuns := MergedAlternativesGroups.columns_cover (EpsilonUnion.Accepts (graph state meaning))
      ((first :: rest).map EdgeValue.children) edge.children terms (List.mem_map.mpr ⟨edge, member, rfl⟩) runs
    simpa only [arity, columns, id] using columnRuns

end
end MicroCFTA.MergedAdaptiveEdges
