import MicroCFTA.InternedNormalizationDepth

/-!
# Exact cached depth through source union normalization

A positive cached depth has a stored Mu descendant with that depth.
Source union construction and root self-reference removal retain each such
descendant. Their existing upper bounds therefore give exact depths.
-/
namespace MicroCFTA.InternedNormalizationDepthExact
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedUnionSeparation InternedUnionDescendants InternedNormalizationDepth
open InternedLiveEdges InternedEdgeResidency
open InternedBinderProtocol (NodeKey Reference)

/-- A positive maximum is attained by one actual input record. -/
theorem maximumDepth_attained (values : List (Value Symbol Guard))
    (positive : 0 < maximumDepth values) :
    ∃ value ∈ values, value.depth = maximumDepth values := by
  classical
  apply Classical.byContradiction
  intro absent
  have bound : maximumDepth values ≤ maximumDepth values - 1 := by
    apply (maximumDepth_exact _ _).mpr
    intro value member
    have upper := (maximumDepth_exact values _).mp (Nat.le_refl _) value member
    have different : value.depth ≠ maximumDepth values := by
      intro same
      exact absent ⟨value, member, same⟩
    omega
  omega

/-- An ordinary readback has the exact depth of its canonical surviving children. -/
theorem makeNode_depth [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    (run (makeNode edges) state).1.depth =
      maximumDepth ((canonicalEdges (surviving edges)).flatMap EdgeValue.children) := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · rename_i same
    simp [run, Value.depth, same, maximumDepth]
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback
      (first :: rest) state coherent linked (by simpa [same] using selected)
    simp only [run, exactResult, identifyNode, Value.depth, same]

/-- Every positive source depth is the depth of a retained Mu record. -/
theorem depth_witness (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) (positive : 0 < value.depth) :
    ∃ entry body depth ordinary, Retains (.mu entry body depth ordinary) value ∧
      (Value.mu entry body depth ordinary).depth = value.depth := by
  cases value with
  | empty | reference => simp [Value.depth] at positive
  | mu entry body depth ordinary => exact ⟨entry, body, depth, ordinary, .here, rfl⟩
  | node entry edges level free =>
      obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
      have equal : level = maximumDepth (edges.flatMap EdgeValue.children) := fields.2.2.1
      obtain ⟨child, member, same⟩ := maximumDepth_attained (edges.flatMap EdgeValue.children)
        (by simpa only [Value.depth, equal] using positive)
      have childDepth : child.depth = level := same.trans equal.symm
      have childAvailable := available.children child member
      obtain ⟨inner, body, depth, ordinary, path, exactDepth⟩ :=
        depth_witness state coherent child childAvailable (by simpa only [childDepth, Value.depth] using positive)
      exact ⟨inner, body, depth, ordinary, .step member path, exactDepth.trans childDepth⟩
  | union entry members level free =>
      obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
      have equal : level = maximumDepth members := fields.2.2.1
      obtain ⟨child, member, same⟩ := maximumDepth_attained members
        (by simpa only [Value.depth, equal] using positive)
      have childDepth : child.depth = level := same.trans equal.symm
      obtain ⟨inner, body, depth, ordinary, path, exactDepth⟩ :=
        depth_witness state coherent child (available.children child member)
          (by simpa only [childDepth, Value.depth] using positive)
      exact ⟨inner, body, depth, ordinary, .step member path, exactDepth.trans childDepth⟩
termination_by sizeOf value
decreasing_by
  · obtain ⟨edge, included, selected⟩ := List.mem_flatMap.mp member
    have edgeSmall := List.sizeOf_lt_of_mem included
    cases edge with
    | mk entry children =>
        have childSmall := List.sizeOf_lt_of_mem selected
        simp only [EdgeValue.children, EdgeValue.mk.sizeOf_spec] at childSmall edgeSmall
        simp_all only [Value.node.sizeOf_spec]
        omega
  · have childSmall := List.sizeOf_lt_of_mem member
    simp_all only [Value.union.sizeOf_spec]
    omega

/-- Source union construction preserves the maximum depth of all input records. -/
theorem makeUnion_depth [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : ∀ value ∈ values, Available state value) :
    (run (makeUnion values) state).1.depth = maximumDepth values := by
  apply Nat.le_antisymm
  · exact makeUnion_depth_le values state coherent cached linked available _
      ((maximumDepth_exact values _).mp (Nat.le_refl _))
  · apply (maximumDepth_exact values _).mpr
    intro value member
    by_cases zero : value.depth = 0
    · simp [zero]
    · obtain ⟨entry, body, depth, ordinary, retained, same⟩ :=
        depth_witness state coherent value (available value member) (by omega)
      have path := makeUnion_retains_mu state coherent cached linked live values available
        entry body depth ordinary value member retained
      have result := makeUnion_available values state coherent cached available
      have bound := retained_depth _ result.1 _ _ result.2.2 path
      simpa only [same] using bound

/-- Removing a bare self alternative preserves the exact cached Mu depth. -/
theorem filter_depth [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (linked : Linked state) (live : Live state) (available : Available state value) :
    (run (withoutSelfReference name value) state).1.depth = value.depth := by
  apply Nat.le_antisymm
  · exact filter_depth_le name value state coherent cached linked available
  · by_cases zero : value.depth = 0
    · simp [zero]
    · obtain ⟨entry, body, depth, ordinary, retained, same⟩ :=
        depth_witness state coherent value available (by omega)
      have path := InternedUnionDescendants.filter_retains_mu state coherent cached linked live
        name value available entry body depth ordinary retained
      have result := InternedTemplateProvenance.withoutSelfReference_available name value state coherent cached available
      have bound := retained_depth _ result.1 _ _ result.2.2 path
      simpa only [same] using bound

end MicroCFTA.InternedNormalizationDepthExact
