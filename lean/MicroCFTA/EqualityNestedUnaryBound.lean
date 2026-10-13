import MicroCFTA.EqualityNestedUnaryMeet

/-!
# Derived source merge bound for every generated nested endpoint

Canonical readback removes repeated rows. A complete unary row is uniquely
determined by its generated child residual. At most two original outer
atoms therefore give at most four actual parent rows. The current target
merge returns every such endpoint and its actual cache unchanged.
-/
namespace MicroCFTA.EqualityNestedUnaryBound
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryChild EqualityNestedUnaryProduct EqualityMergedTargetReadback
open EqualityMergedTargetLayers EqualityMergedTargetFixedPoint

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Exact ordinary readback has no duplicate complete outgoing rows. -/
theorem normal_nodup (value : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (available : Available state value) (normal : Replayable value) : (nodeEdges value).Nodup := by
  have readback := replayable_normal value normal state facts available
  have result := EqualityLeafProjectionPhysical.makeNode_edges (nodeEdges value) state facts.coherent facts.linked
    (resident_edges state facts.linked value available.resident)
  rw [readback] at result
  rw [result]
  exact MergedNodeRowBounds.canonical_nodup _

/-- Injective generated residual codes bound the number of actual canonical parent rows. -/
theorem rows_bound (parent leaf : Fin symbols) (selected : Node initial) (value : Value (Fin symbols) ConstraintKey)
    (shape : NodeShape parent leaf selected value) (normal : Replayable value)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (available : Available state value) :
    (nodeEdges value).length ≤ (inventory initial).length := by
  classical
  by_cases empty : nodeEdges value = []
  · simp [empty]
  obtain ⟨first, member⟩ := List.exists_mem_of_ne_nil _ empty
  obtain ⟨fallback, _, fallbackShape⟩ := shape.sound first member
  let code := fun edge => if existsRow : ∃ row : Row initial, RowShape parent leaf row edge then Classical.choose existsRow else fallback
  have represented : ∀ edge ∈ nodeEdges value, RowShape parent leaf (code edge) edge := by
    intro edge present
    obtain ⟨row, _, rowShape⟩ := shape.sound edge present
    have witness : ∃ row : Row initial, RowShape parent leaf row edge := ⟨row, rowShape⟩
    simpa only [code, dite_eq_left witness] using Classical.choose_spec witness
  have distinct : ((nodeEdges value).map code).Nodup := by
    apply List.pairwise_map.mpr
    exact (normal_nodup value state facts available normal).imp_of_mem
      (fun leftMember rightMember different same => different
        (row_unique parent leaf _ _ _ state facts
          (resident_edges state facts.linked value available.resident _ leftMember)
          (resident_edges state facts.linked value available.resident _ rightMember)
          (represented _ leftMember) (same ▸ represented _ rightMember)))
  have bound := distinct.length_le_of_subset (l₂ := inventory initial) (fun row _ => inventory_complete initial row)
  simpa only [List.length_map] using bound

/-- Exact readback and small rows preserve recursive exactness when all children are exact. -/
theorem normal_small (value : Value (Fin symbols) ConstraintKey) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) (normal : Replayable value)
    (small : (nodeEdges value).length ≤ 4)
    (children : ∀ edge ∈ nodeEdges value, ∀ child ∈ edge.children, Normal Exact child) : Normal Exact value := by
  have readback := replayable_normal value normal state facts available
  obtain ⟨bound, output, after, done, extension, property⟩ := makeNode_exact (nodeEdges value) state facts prepared
    (resident_edges state facts.linked value available.resident) small children
  have result := done bound (Nat.le_refl _)
  change run (makeNode (nodeEdges value)) state = (value, state) at readback
  simp only [MergedColdMerge.work, readback, Result.done.injEq] at result
  obtain ⟨rfl, rfl⟩ := result
  exact property.2

/-- A canonical singleton nullary child already satisfies every target-merge normality layer. -/
theorem leaf_normal (symbol : Fin symbols) (row : Row initial) (value : Value (Fin symbols) ConstraintKey)
    (represented : LeafRow symbol row value) (normal : Replayable value)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) : Normal Exact value := by
  have resident := resident_edges state facts.linked value available.resident
  obtain ⟨first, firstMember, firstKey⟩ := (represented (EqualityLeafProjectionLeafCache.key symbol row)).mpr rfl
  have keys : ∀ edge ∈ nodeEdges value, edge.entry.key = first.entry.key := by
    intro edge member
    exact ((represented edge.entry.key).mp ⟨edge, member, rfl⟩).trans firstKey.symm
  have subset : nodeEdges value ⊆ [first] := by
    intro edge member
    have stored := resident edge member
    change state.edgeRecords edge.entry.key = some edge at stored
    rw [keys edge member, resident first firstMember] at stored
    exact List.mem_singleton.mpr (Option.some.inj stored).symm
  have small := (normal_nodup value state facts available normal).length_le_of_subset subset
  apply normal_small value state facts prepared available normal (by simpa using Nat.le_trans small (show [first].length ≤ 4 by simp))
  intro edge member child included
  have fields := (facts.coherent.edges edge.entry.key edge (resident edge member)).2.2
  have key := (represented edge.entry.key).mp ⟨edge, member, rfl⟩
  have noChildren : edge.children = [] := by
    apply List.map_eq_nil_iff.mp
    simpa only [key, EqualityLeafProjectionLeafCache.key] using fields
  simp [noChildren] at included

/-- Every canonical represented endpoint in the generated four-row carrier is already merge-exact. -/
theorem node_normal (parent leaf : Fin symbols) (selected : Node initial) (value : Value (Fin symbols) ConstraintKey)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (shape : NodeShape parent leaf selected value) (normal : Replayable value)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) : Normal Exact value := by
  apply normal_small value state facts prepared available normal
    (Nat.le_trans (rows_bound parent leaf selected value shape normal state facts available) (inventory_bound initial small))
  intro edge member child included
  obtain ⟨row, _, _, _, other, children, represented, replay⟩ := shape.sound edge member
  have same := List.mem_singleton.mp (children ▸ included)
  subst child
  exact leaf_normal leaf row other represented replay state facts prepared
    (facts.cached.edges edge.entry.key edge (resident_edges state facts.linked value available.resident edge member) other (by simp [children]))

/-- Actual source target merging is the exact identity at every comparison fuel in this derived fragment. -/
theorem merge_fixed (parent leaf : Fin symbols) (selected : Node initial) (value : Value (Fin symbols) ConstraintKey)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (shape : NodeShape parent leaf selected value) (normal : Replayable value)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (clear : ConstraintKey → Bool) (top : ConstraintKey) (comparison : Nat) :
    execute MergedSourceGrouping.groups clear top comparison value state = .done value state :=
  execute_fixed clear top comparison value (node_normal parent leaf selected value small shape normal state facts prepared available)
    state facts prepared available

end MicroCFTA.EqualityNestedUnaryBound
