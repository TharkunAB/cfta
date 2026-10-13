import MicroCFTA.MergedPhysicalUnionTransport
import MicroCFTA.EqualityLeafProjectionPhysical
import MicroCFTA.InternedUnionFilterFusion

/-!
# Exact language of the actual union constructor

Union construction flattens stored unions and removes duplicate identities.
The ordinary branch combines the stored edges. Complete cache readback
preserves these records. Empty-child removal drops only impossible runs.
-/
namespace MicroCFTA.MergedPhysicalUnion
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedUnionRetention InternedUnionFilterFusion
open MergedPhysicalComparison MergedPhysicalLanguage MergedPhysicalMergeContext
open EqualityLeafProjectionPhysical Language

/-- A complete source edge accepts its ordered child terms and its full guard. -/
def EdgeAccepts [DecidableEq (EdgeKey Symbol Guard)]
    (view : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard) (term : Term Symbol) : Prop :=
  ∃ terms, term = .node edge.entry.key.symbol terms ∧
    All₂ (EpsilonUnion.Accepts (graph view meaning)) edge.children terms ∧
    meaning edge.entry.key.constraint term = true

/-- Literal EmptyNode has no finite accepting run. -/
theorem empty_rejects [DecidableEq (EdgeKey Symbol Guard)]
    (view : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    ¬ EpsilonUnion.Accepts (graph view meaning) .empty term := by
  intro accepted
  cases accepted with
  | reference member => simp [graph, successors] at member
  | node edge children member => simp [graph, constructorRows] at member

/-- An ordinary complete record accepts exactly one of its stored edges. -/
theorem node_exact [DecidableEq (EdgeKey Symbol Guard)]
    (view : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (term : Term Symbol) :
    EpsilonUnion.Accepts (graph view meaning) (.node entry edges depth free) term ↔
      ∃ edge ∈ edges, EdgeAccepts view meaning edge term := by
  constructor
  · intro accepted
    cases accepted with
    | reference member => simp [graph, successors] at member
    | node edge terms member subtrees guard =>
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact ⟨original, present, terms, rfl, subtrees, guard⟩
  · rintro ⟨edge, member, terms, rfl, subtrees, guard⟩
    exact .node ⟨edge.entry.key.symbol, edge.children, meaning edge.entry.key.constraint⟩ terms
      (List.mem_map.mpr ⟨edge, member, rfl⟩) subtrees guard

/-- An accepted edge has no literal empty child. -/
theorem accepted_live [DecidableEq (EdgeKey Symbol Guard)]
    (view : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard) (term : Term Symbol)
    (accepted : EdgeAccepts view meaning edge term) : dead edge = false := by
  obtain ⟨terms, _, runs, _⟩ := accepted
  apply Bool.eq_false_iff.mpr
  intro isDead
  obtain ⟨child, included, empty⟩ := List.any_eq_true.mp isDead
  have same : child = .empty := (reference_empty child).mp (beq_iff_eq.mp empty)
  obtain ⟨subterm, _, childRun⟩ := SymbolicSmartRows.all₂_child _ _ _ runs child included
  rw [same] at childRun
  exact empty_rejects view meaning subterm childRun

/-- Canonical ordering and dead-edge removal preserve the exact edge language. -/
theorem normalized_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state view : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges state edges)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    (∃ edge ∈ canonicalEdges (surviving edges), EdgeAccepts view meaning edge term) ↔
      ∃ edge ∈ edges, EdgeAccepts view meaning edge term := by
  constructor
  · rintro ⟨edge, member, accepted⟩
    exact ⟨edge, ((normalized_member state facts.coherent edges resident edge).mp member).1, accepted⟩
  · rintro ⟨edge, member, accepted⟩
    exact ⟨edge, (normalized_member state facts.coherent edges resident edge).mpr
      ⟨member, accepted_live view meaning edge term accepted⟩, accepted⟩

/-- Actual ordinary node construction has the requested edge language in any common cache. -/
theorem makeNode_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state view : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges state edges)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph view meaning) (run (makeNode edges) state).1 term ↔
      ∃ edge ∈ edges, EdgeAccepts view meaning edge term := by
  rw [← normalized_exact state view facts edges resident meaning term]
  have selected : Edges state (canonicalEdges (surviving edges)) :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  cases kept : canonicalEdges (surviving edges) with
  | nil => simp [makeNode, kept, run, empty_rejects]
  | cons first rest =>
      obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
        (by simpa only [Edges, kept] using selected)
      simp only [makeNode, kept, run, readback, identifyNode]
      exact node_exact view meaning entry _ _ _ term

/-- Flattening a stored union keeps its exact operand language. -/
theorem flatten_one [DecidableEq (EdgeKey Symbol Guard)]
    (view : InternedConstructorTemplates.State Symbol Guard) (meaning : Guard → Term Symbol → Bool)
    (value : Value Symbol Guard) (term : Term Symbol) :
    (∃ member ∈ unionMembers value, EpsilonUnion.Accepts (graph view meaning) member term) ↔
      EpsilonUnion.Accepts (graph view meaning) value term := by
  cases value with
  | empty => simp [unionMembers, empty_rejects]
  | reference | node | mu => simp only [unionMembers, List.mem_singleton, exists_eq_left]
  | union entry members depth free => exact (retained_union_exact view meaning entry members depth free term).symm

/-- Flattening and physical identity deduplication preserve the exact operand language. -/
theorem selected_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state view : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (inputs : Values state values)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    (∃ member ∈ distinctNodes (values.flatMap unionMembers), EpsilonUnion.Accepts (graph view meaning) member term) ↔
      ∃ member ∈ values, EpsilonUnion.Accepts (graph view meaning) member term := by
  have flatAvailable : Values state (values.flatMap unionMembers) := by
    intro value member
    obtain ⟨source, original, selected⟩ := List.mem_flatMap.mp member
    exact unionMembers_available source (inputs source original) value selected
  constructor
  · rintro ⟨member, present, accepted⟩
    obtain ⟨source, original, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ member present)
    exact ⟨source, original, (flatten_one view meaning source term).mp ⟨member, selected, accepted⟩⟩
  · rintro ⟨source, original, accepted⟩
    obtain ⟨member, selected, accepted⟩ := (flatten_one view meaning source term).mpr accepted
    exact ⟨member, distinctNodes_retains state facts.coherent _
      (fun value included => (flatAvailable value included).resident) member
      (List.mem_flatMap.mpr ⟨source, original, selected⟩), accepted⟩

/-- The ordinary fast path concatenates exactly the operand edge languages. -/
theorem ordinary_exact [DecidableEq (EdgeKey Symbol Guard)]
    (view : InternedConstructorTemplates.State Symbol Guard) (meaning : Guard → Term Symbol → Bool)
    (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (found : ordinaryEdges values = some edges) (term : Term Symbol) :
    (∃ edge ∈ edges, EdgeAccepts view meaning edge term) ↔
      ∃ value ∈ values, EpsilonUnion.Accepts (graph view meaning) value term := by
  induction values generalizing edges with
  | nil => simp only [ordinaryEdges, Option.some.injEq] at found; subst edges; simp
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      rename_i entry own depth free
      cases tail : ordinaryEdges rest with
      | none => simp [tail] at found
      | some later =>
          simp only [tail, Option.map_some, Option.some.injEq] at found
          subst edges
          simp only [List.mem_append, List.mem_cons]
          constructor
          · rintro ⟨edge, before | after, accepted⟩
            · exact ⟨_, Or.inl rfl, (node_exact view meaning entry own depth free term).mpr ⟨edge, before, accepted⟩⟩
            · obtain ⟨value, member, accepted⟩ := (ih later tail).mp ⟨edge, after, accepted⟩
              exact ⟨value, Or.inr member, accepted⟩
          · rintro ⟨value, same | member, accepted⟩
            · subst value
              obtain ⟨edge, member, accepted⟩ := (node_exact view meaning entry own depth free term).mp accepted
              exact ⟨edge, Or.inl member, accepted⟩
            · obtain ⟨edge, member, accepted⟩ := (ih later tail).mpr ⟨value, member, accepted⟩
              exact ⟨edge, Or.inr member, accepted⟩

/-- Actual union readback denotes exactly its original operands in any common cache. -/
theorem makeUnion_common [DecidableEq (EdgeKey Symbol Guard)]
    (state view : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (inputs : Values state values)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph view meaning) (run (makeUnion values) state).1 term ↔
      ∃ value ∈ values, EpsilonUnion.Accepts (graph view meaning) value term := by
  rw [← selected_exact state view facts values inputs meaning term]
  cases selected : distinctNodes (values.flatMap unionMembers) with
  | nil => simp [makeUnion, selected, run, empty_rejects]
  | cons first rest =>
      cases rest with
      | nil => simp only [makeUnion, selected, run, List.mem_singleton, exists_eq_left]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | none =>
              obtain ⟨entry, readback⟩ := union_readback values first second tail state facts inputs selected ordinary
              rw [readback]
              exact retained_union_exact view meaning entry _ _ _ term
          | some edges =>
              have available : Values state (first :: second :: tail) := by
                simpa only [selected] using selected_available values state inputs
              have resident := ordinaryEdges_resident _ edges state facts.linked
                (fun value member => (available value member).resident) ordinary
              simp only [makeUnion, selected, ordinary]
              exact (makeNode_exact state view facts edges resident meaning term).trans
                (ordinary_exact view meaning _ edges ordinary term)

/-- The prepared source constructor preserves operand languages in its actual returned cache. -/
theorem makeUnion_actual [DecidableEq (EdgeKey Symbol Guard)]
    (state : InternedConstructorTemplates.State Symbol Guard) (outputs : List (Value Symbol Guard))
    (context : Context state outputs) (values : List (Value Symbol Guard)) (inputs : Values state values)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    let result := run (makeUnion values) state
    Context result.2 outputs ∧ Available result.2 result.1 ∧
      (EpsilonUnion.Accepts (graph result.2 meaning) result.1 term ↔
        ∃ value ∈ values, EpsilonUnion.Accepts (graph state meaning) value term) := by
  have built := context.makeUnion state outputs values inputs
  refine ⟨built.1, built.2, ?_⟩
  rw [makeUnion_common state _ context.facts values inputs meaning term]
  exact exists_congr fun value => and_congr_right fun member =>
    MergedPhysicalUnionTransport.accepts_stable state _ outputs context
      (InternedConstructorTemplates.run_correct (makeUnion values) state context.facts.coherent.valid).2
      meaning value (inputs value member) term

end MicroCFTA.MergedPhysicalUnion
