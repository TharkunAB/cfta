import MicroCFTA.MergedSourceSelectionSemantics
import MicroCFTA.MergedPhysicalGroupColumnWorker

/-!
# Common-cache language laws for cold merge constructors

Every operand and result uses one common source cache. These laws do not
transport the raw graph of an earlier cold cache through allocation.
They apply after the actual ordered selection and recursive calls.
-/
namespace MicroCFTA.MergedColdMergeLanguage
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedPhysicalLanguage MergedPhysicalUnion
open MergedPhysicalGroupCalls MergedPhysicalGroupEdges MergedPhysicalGroupColumns MergedOrdinaryHeight
open Language

/-- Actual ordinary union is exact when its ordinary operands and result use the same observation cache. -/
theorem ordinaryUnion_common [DecidableEq (EdgeKey Symbol Guard)]
    (state view : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (available : Values state values)
    (ordinary : ∀ value ∈ values, value = .empty ∨ ∃ entry edges depth free, value = .node entry edges depth free)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph view meaning) (run (ordinaryUnion values) state).1 term ↔
      ∃ value ∈ values, EpsilonUnion.Accepts (graph view meaning) value term := by
  let edges := values.flatMap nodeEdges
  have resident : Edges state edges := by
    intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact resident_edges state facts.linked value (available value present).resident edge included
  change EpsilonUnion.Accepts (graph view meaning) (run (makeNode edges) state).1 term ↔ _
  rw [makeNode_exact state view facts edges resident meaning term]
  constructor
  · rintro ⟨edge, member, accepted⟩
    obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
    rcases ordinary value included with same | ⟨entry, own, depth, free, same⟩
    · subst value
      simp [nodeEdges] at present
    · subst value
      exact ⟨_, included, (node_exact view meaning entry own depth free term).mpr ⟨edge, present, accepted⟩⟩
  · rintro ⟨value, included, accepted⟩
    rcases ordinary value included with same | ⟨entry, own, depth, free, same⟩
    · subst value
      exact False.elim (empty_rejects view meaning term accepted)
    · subst value
      obtain ⟨edge, present, accepted⟩ := (node_exact view meaning entry own depth free term).mp accepted
      exact ⟨edge, List.mem_flatMap.mpr ⟨_, included, present⟩, accepted⟩

/-- Coverage of the ordinary union result includes each original operand in the same cache. -/
theorem ordinaryUnion_covers [DecidableEq (EdgeKey Symbol Guard)]
    (state view : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (available : Values state values)
    (ordinary : ∀ value ∈ values, value = .empty ∨ ∃ entry edges depth free, value = .node entry edges depth free)
    (meaning : Guard → Term Symbol → Bool) (result : Value Symbol Guard)
    (covered : Covers view view meaning [(run (ordinaryUnion values) state).1] result) :
    Covers view view meaning values result := by
  intro value member term accepted
  exact covered _ List.mem_cons_self term
    ((ordinaryUnion_common state view facts values available ordinary meaning term).mpr ⟨value, member, accepted⟩)

/-- Exact source selection composes with a covering retained-column result in the same later cache. -/
theorem selected_covers [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (prepared : Prepared state) (available : Values state inputs)
    (retained : List (Value Symbol Guard)) (after view : InternedConstructorTemplates.State Symbol Guard)
    (done : MergedSourceSelection.select clear fuel inputs state = .done retained after)
    (growth : Grows after view) (viewFacts : Facts view) (viewPrepared : Prepared view) (viewInputs : Values view inputs)
    (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (result : Value Symbol Guard) (covered : Covers view view meaning retained result) :
    Covers view view meaning inputs result := by
  intro value member term accepted
  obtain ⟨kept, selected, accepted⟩ :=
    (MergedSourceSelectionSemantics.select_exact clear fuel inputs state facts prepared available retained after view
      done growth viewFacts viewPrepared viewInputs meaning clearTrue term).mpr ⟨value, member, accepted⟩
  exact covered kept selected term accepted

/-- Actual small-edge construction preserves each original row after common-cache child coverage. -/
theorem small_edge_covers [DecidableEq (EdgeKey Symbol Guard)]
    (state view : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (edge : EdgeValue Symbol Guard) (values : List (Value Symbol Guard)) (available : Values state values)
    (meaning : Guard → Term Symbol → Bool)
    (covered : All₂ (fun original result => Covers view view meaning [original] result) edge.children values)
    (term : Term Symbol) (accepted : EdgeAccepts view meaning edge term) :
    EdgeAccepts view meaning (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) state).1 term := by
  have fields := makeEdge_fields state facts edge.entry.key.symbol edge.entry.key.constraint values available
  obtain ⟨terms, shape, runs, guard⟩ := accepted
  refine ⟨terms, by rw [fields.1]; exact shape, ?_, by rw [fields.2.1]; exact guard⟩
  rw [fields.2.2]
  apply covers_runs view view meaning (fun value => [value]) edge.children values terms covered
  exact runs.imp (fun value term accepted => ⟨value, List.mem_cons_self, accepted⟩)

/-- Common-cache column coverage includes every row in an unconstrained large source group. -/
theorem large_edge_covers [DecidableEq (EdgeKey Symbol Guard)]
    (state view : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) (keys : SameKey (first :: rest))
    (values : List (Value Symbol Guard)) (available : Values state values)
    (meaning : Guard → Term Symbol → Bool) (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (covered : All₂ (fun column result => Covers view view meaning column result)
      (MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length) values)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ first :: rest)
    (term : Term Symbol) (accepted : EdgeAccepts view meaning edge term) :
    EdgeAccepts view meaning (run (makeEdge first.entry.key.symbol top values) state).1 term := by
  have fields := makeEdge_fields state facts first.entry.key.symbol top values available
  obtain ⟨terms, shape, runs, _⟩ := accepted
  obtain ⟨symbol, arity⟩ := keys edge member first List.mem_cons_self
  refine ⟨terms, by rw [fields.1, ← symbol]; exact shape, ?_, by rw [fields.2.1]; exact topTrue term⟩
  rw [fields.2.2]
  apply covers_runs view view meaning id _ values terms covered
  have columns := MergedAlternativesGroups.columns_cover (EpsilonUnion.Accepts (graph view meaning))
    ((first :: rest).map EdgeValue.children) edge.children terms (List.mem_map.mpr ⟨edge, member, rfl⟩) runs
  simpa only [arity, id] using columns

/-- Actual parent-node construction includes all original rows covered by the returned group edges. -/
theorem node_covers [DecidableEq (EdgeKey Symbol Guard)]
    (state view : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (original : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges state edges)
    (meaning : Guard → Term Symbol → Bool)
    (covered : ∀ edge ∈ original, ∀ term, EdgeAccepts view meaning edge term →
      ∃ result ∈ edges, EdgeAccepts view meaning result term) :
    Covers view view meaning [.node entry original depth free] (run (makeNode edges) state).1 := by
  intro value member term accepted
  rw [List.mem_singleton.mp member] at accepted
  obtain ⟨edge, member, accepted⟩ := (node_exact view meaning entry original depth free term).mp accepted
  exact (makeNode_exact state view facts edges resident meaning term).mpr (covered edge member term accepted)

end MicroCFTA.MergedColdMergeLanguage
