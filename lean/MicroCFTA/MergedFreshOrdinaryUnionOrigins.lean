import MicroCFTA.MergedFreshOrdinaryGraphOrigins
import MicroCFTA.InternedUnionFilterFusion
import MicroCFTA.InternedStoredPlanBinderDepthExact
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Actual union normalization preserves complete repaired edge origins

The proof follows flattening, identity deduplication, and both constructor
branches. Live stored rows ensure that an ordinary merge deletes no source
edge. Every equation retains the complete physical edge, including its guard
and ordered child identities. No input-product language premise is used.
-/
namespace MicroCFTA.MergedFreshOrdinaryUnionOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedLiveEdges
open InternedUnionRetention InternedUnionFilterFusion EqualityLeafProjectionPhysical
open MergedFreshOrdinaryGraph

/-- Actual union flattening retains precisely the complete origins of one operand. -/
theorem flatten_origins [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (value : Value Symbol Guard) (edge : EdgeValue Symbol Guard) :
    (∃ member ∈ unionMembers value, Origin view [member] edge) ↔ Origin view [value] edge := by
  cases value with
  | empty => simp [unionMembers, origin_empty]
  | reference | node | mu => simp only [unionMembers, List.mem_singleton, exists_eq_left]
  | union entry members depth free => exact (origin_union view entry members depth free edge).symm

/-- Flattening and actual identity deduplication preserve every complete repaired origin. -/
theorem selected_origins [DecidableEq (EdgeKey Symbol Guard)] (state view : State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (available : Values state values) (edge : EdgeValue Symbol Guard) :
    (∃ member ∈ distinctNodes (values.flatMap unionMembers), Origin view [member] edge) ↔
      ∃ member ∈ values, Origin view [member] edge := by
  have flatAvailable : Values state (values.flatMap unionMembers) := by
    intro value member
    obtain ⟨source, present, selected⟩ := List.mem_flatMap.mp member
    exact unionMembers_available source (available source present) value selected
  constructor
  · rintro ⟨member, present, origin⟩
    obtain ⟨source, original, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ member present)
    exact ⟨source, original, (flatten_origins view source edge).mp ⟨member, selected, origin⟩⟩
  · rintro ⟨source, present, origin⟩
    obtain ⟨member, selected, origin⟩ := (flatten_origins view source edge).mpr origin
    exact ⟨member, distinctNodes_retains state facts.coherent _
      (fun value included => (flatAvailable value included).resident) member
      (List.mem_flatMap.mpr ⟨source, present, selected⟩), origin⟩

/-- The ordinary merge reads exactly the complete origins of its literal node operands. -/
theorem ordinary_origins [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (found : ordinaryEdges values = some edges) (edge : EdgeValue Symbol Guard) :
    edge ∈ edges ↔ ∃ value ∈ values, Origin view [value] edge := by
  induction values generalizing edges with
  | nil => cases found; simp
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      rename_i entry own depth free
      cases tail : ordinaryEdges rest with
      | none => simp [tail] at found
      | some later =>
          have same : own ++ later = edges := by simpa only [tail, Option.map_some, Option.some.injEq] using found
          subst edges
          simp only [List.mem_append, List.mem_cons]
          constructor
          · rintro (present | present)
            · exact ⟨_, Or.inl rfl, (origin_node view entry own depth free edge).mpr present⟩
            · obtain ⟨value, present, origin⟩ := (ih later tail).mp present
              exact ⟨value, Or.inr present, origin⟩
          · rintro ⟨value, same | present, origin⟩
            · subst value
              exact Or.inl ((origin_node view entry own depth free edge).mp origin)
            · exact Or.inr ((ih later tail).mpr ⟨value, present, origin⟩)

/-- Canonical node construction retains every complete row when its source filter deletes no row. -/
theorem node_origins [DecidableEq (EdgeKey Symbol Guard)] (state view : State Symbol Guard) (facts : Facts state)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges state edges) (live : surviving edges = edges)
    (edge : EdgeValue Symbol Guard) :
    Origin view [(run (makeNode edges) state).1] edge ↔ edge ∈ edges := by
  have exactRows : edge ∈ canonicalEdges (surviving edges) ↔ edge ∈ edges := by
    rw [live]
    exact ⟨canonicalEdges_member edges edge, canonicalEdges_retains state facts.coherent edges edge resident⟩
  rw [← exactRows]
  have selected : Edges state (canonicalEdges (surviving edges)) :=
    fun row member => resident row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
  cases kept : canonicalEdges (surviving edges) with
  | nil => simp [makeNode, kept, run, origin_empty]
  | cons first rest =>
      obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
        (by simpa only [Edges, kept] using selected)
      simp only [makeNode, kept, run, readback, identifyNode]
      exact origin_node view entry _ _ _ edge

/-- Actual union normalization preserves exactly all complete repaired epsilon origins of its original operands. -/
theorem union_origins [DecidableEq (EdgeKey Symbol Guard)] (state view : State Symbol Guard)
    (facts : Facts state) (live : Live state) (values : List (Value Symbol Guard))
    (available : Values state values) (edge : EdgeValue Symbol Guard) :
    Origin view [(run (makeUnion values) state).1] edge ↔ ∃ value ∈ values, Origin view [value] edge := by
  rw [← selected_origins state view facts values available edge]
  cases selected : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, selected, run, origin_empty]
  | cons first rest =>
      cases rest with
      | nil => simp only [makeUnion, selected, run, List.mem_singleton, exists_eq_left]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | none =>
              obtain ⟨entry, readback⟩ := union_readback values first second tail state facts available selected ordinary
              rw [readback]
              exact origin_union view entry _ _ _ edge
          | some edges =>
              have inputs : Values state (first :: second :: tail) := by
                simpa only [selected] using selected_available values state available
              have resident := ordinaryEdges_resident _ edges state facts.linked
                (fun value member => (inputs value member).resident) ordinary
              have retained := InternedStoredPlanBinderDepth.ordinaryEdges_surviving _ edges state live inputs ordinary
              simp only [makeUnion, selected, ordinary]
              exact (node_origins state view facts edges resident retained edge).trans
                (ordinary_origins view _ edges ordinary edge)

end MicroCFTA.MergedFreshOrdinaryUnionOrigins
