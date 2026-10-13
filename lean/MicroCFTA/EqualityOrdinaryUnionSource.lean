import MicroCFTA.EqualityOrdinaryReadback

/-!
# The ordinary Operations.union branch and the union constructor

Operations.union concatenates ordinary outgoing edges before makeNode.
The constructor also removes empty and duplicate operands and has a
singleton shortcut. Complete resident normal operands give exactly the
same result and cache effects for both implementations.
-/
namespace MicroCFTA.EqualityOrdinaryUnionSource
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open InternedFreshProbeKeys InternedProbeProvenance
open EqualityLeafProjectionUnion EqualityOrdinaryReadback

/-- The actual source union branch for ordinary operands. -/
def sourceUnion (values : List (Value Symbol Guard)) : Work Symbol Guard (Value Symbol Guard) :=
  makeNode (values.flatMap nodeEdges)

/-- The source ordinary union preserves all complete resident payload facts. -/
theorem sourceUnion_available [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : EqualityLeafProjectionCompileAvailability.Facts state)
    (available : ∀ value ∈ values, Available state value) :
    EqualityLeafProjectionCompileAvailability.Facts (run (sourceUnion values) state).2 ∧
      Available (run (sourceUnion values) state).2 (run (sourceUnion values) state).1 := by
  have edgeResident : ∀ edge ∈ values.flatMap nodeEdges, EdgeResident state edge := by
    intro edge member
    obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
    exact resident_edges state facts.linked value (available value included).resident edge present
  have childrenAvailable : ∀ child ∈ (values.flatMap nodeEdges).flatMap EdgeValue.children, Available state child := by
    intro child member
    obtain ⟨edge, included, present⟩ := List.mem_flatMap.mp member
    exact facts.cached.edges edge.entry.key edge (edgeResident edge included) child present
  have checked := makeNode_available (values.flatMap nodeEdges) state facts.coherent facts.cached childrenAvailable
  exact ⟨⟨checked.1, checked.2.1, makeNode_linked _ state facts.linked edgeResident⟩, checked.2.2⟩

/-- Ordinary source union and normalized constructor union have identical complete runs. -/
theorem union_run [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ value ∈ values, Resident state value)
    (ordinary : ∀ value ∈ values, OrdinaryRoot value)
    (normal : ∀ value ∈ values, Normal state value) :
    run (sourceUnion values) state = run (makeUnion values) state := by
  let flat := values.flatMap unionMembers
  let members := distinctNodes flat
  have flatFacts : ∀ value ∈ flat, value ∈ values ∧ NodeRoot value := by
    intro value member
    obtain ⟨source, included, selected⟩ := List.mem_flatMap.mp member
    obtain ⟨rfl, isNode⟩ := ordinary_member source value (ordinary source included) selected
    exact ⟨included, isNode⟩
  have flatResident : ∀ value ∈ flat, Resident state value :=
    fun value member => resident value (flatFacts value member).1
  have selected : ∀ value, value ∈ members ↔ value ∈ flat := by
    intro value
    exact ⟨distinctNodes_member flat value,
      InternedUnionRetention.distinctNodes_retains state coherent flat flatResident value⟩
  have memberFacts : ∀ value ∈ members, value ∈ values ∧ NodeRoot value :=
    fun value member => flatFacts value ((selected value).mp member)
  have sameMembers : ∀ edge, edge ∈ members.flatMap nodeEdges ↔ edge ∈ values.flatMap nodeEdges := by
    intro edge
    constructor
    · intro member
      obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
      exact List.mem_flatMap.mpr ⟨value, (memberFacts value included).1, present⟩
    · intro member
      obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
      have root := ordinary value included
      have flattened : value ∈ unionMembers value := by
        cases value <;> simp_all [OrdinaryRoot, nodeEdges, unionMembers]
      exact List.mem_flatMap.mpr ⟨value,
        (selected value).mpr (List.mem_flatMap.mpr ⟨value, included, flattened⟩), present⟩
  have valuesResident : ∀ edge ∈ values.flatMap nodeEdges, EdgeResident state edge := by
    intro edge member
    obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
    exact resident_edges state linked value (resident value included) edge present
  have memberResident : ∀ edge ∈ members.flatMap nodeEdges, EdgeResident state edge :=
    fun edge member => valuesResident edge ((sameMembers edge).mp member)
  have sameWork := InternedNodeSetCongruence.makeNode_same_members state coherent
    (values.flatMap nodeEdges) (members.flatMap nodeEdges) valuesResident memberResident
    (fun edge => by simp only [surviving, List.mem_filter, sameMembers edge])
  unfold sourceUnion
  rw [sameWork]
  cases shape : members with
  | nil =>
      have sourceShape : distinctNodes (values.flatMap unionMembers) = [] := shape
      simp [makeUnion, sourceShape, makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, run]
  | cons first rest =>
      cases rest with
      | nil =>
          have sourceShape : distinctNodes (values.flatMap unionMembers) = [first] := shape
          have firstMember : first ∈ members := by simp [shape]
          have firstNormal := normal first (memberFacts first firstMember).1
          simpa only [makeUnion, sourceShape, shape, List.flatMap_cons, List.flatMap_nil, List.append_nil, run, Normal] using firstNormal
      | cons second tail =>
          have sourceShape : distinctNodes (values.flatMap unionMembers) = first :: second :: tail := shape
          have sourceEdges : ordinaryEdges (first :: second :: tail) = some (members.flatMap nodeEdges) := by
            rw [← shape]
            exact ordinary_edges members (fun value member => (memberFacts value member).2)
          simp only [makeUnion, sourceShape, sourceEdges, shape]

end MicroCFTA.EqualityOrdinaryUnionSource
