import MicroCFTA.EqualityLeafProjectionReplay

/-!
# Exact physical nullary construction from source row declarations

A source leaf product or union supplies a finite list of symbol and full
constraint pairs. The actual edge and node caches retain exactly this set
of nullary keys after duplicate normalization.
-/
namespace MicroCFTA.EqualityLeafProjectionNullary
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency InternedFreshProbeKeys
open EqualityLeafProjectionPhysical
open EqualityLeafProjectionWorkers (sequence sequence_safe sequence_completed)

/-- A nullary declaration contains every source edge-key field. -/
def key (row : Symbol × Guard) : EdgeKey Symbol Guard := ⟨row.1, [], row.2⟩

/-- The complete nullary key retains its exact declared symbol and constraint. -/
theorem key_injective (first second : Symbol × Guard) (same : key first = key second) : first = second := by
  have symbol := congrArg EdgeKey.symbol same
  have guard := congrArg EdgeKey.constraint same
  exact Prod.ext symbol guard

/-- Execute the source nullary edge requests in their supplied order. -/
def requests (rows : List (Symbol × Guard)) : List (Work Symbol Guard (EdgeValue Symbol Guard)) :=
  rows.map fun (symbol, constraint) => makeEdge symbol constraint []

/-- Physical nullary construction uses the actual separate caches. -/
def build (rows : List (Symbol × Guard)) : Work Symbol Guard (Value Symbol Guard) :=
  (sequence (requests rows)).bind makeNode

/-- Actual nullary readback has its requested complete key and no child records. -/
theorem nullary_fields [DecidableEq (EdgeKey Symbol Guard)] (row : Symbol × Guard)
    (state : State Symbol Guard) (coherent : Coherent state) :
    (run (makeEdge row.1 row.2 []) state).1.entry.key = key row ∧
      (run (makeEdge row.1 row.2 []) state).1.children = [] := by
  let identify := fun entry => EdgeValue.mk entry ([] : List (Value Symbol Guard))
  have correct := edgeStep_correct (key row) identify state coherent.valid
  have after := edgeStep_coherent (key row) identify state coherent (fun _ same => ⟨rfl, same, rfl⟩)
  have fields := (after.edges _ _ correct.2.2).2
  exact ⟨fields.1, List.map_eq_nil_iff.mp fields.2⟩

/-- Every generated row request uses the literal source fields. -/
theorem requests_safe (rows : List (Symbol × Guard)) : ∀ request ∈ requests rows, Safe request := by
  intro request member
  obtain ⟨⟨symbol, guard⟩, _, rfl⟩ := List.mem_map.mp member
  exact makeEdge_safe symbol guard []

/-- Finite row construction retains coherence and all existing node-edge links. -/
theorem rows_linked [DecidableEq (EdgeKey Symbol Guard)] (rows : List (Symbol × Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state) :
    Linked (run (sequence (requests rows)) state).2 := by
  induction rows generalizing state with
  | nil => exact linked
  | cons first rest ih =>
      rcases first with ⟨symbol, guard⟩
      simp only [requests, List.map_cons, sequence, run_bind, run]
      exact ih _ (InternedErasedEdgeReplay.run_coherent _ state (makeEdge_safe _ _ _) coherent)
        (makeEdge_linked symbol guard [] state coherent linked).1

/-- Complete physical row requests recover exactly their original declared key set. -/
theorem completed_rows [DecidableEq (EdgeKey Symbol Guard)] (rows : List (Symbol × Guard))
    (state : State Symbol Guard) (coherent : Coherent state) :
    let result := run (sequence (requests rows)) state
    Coherent result.2 ∧ (∀ edge ∈ result.1, EdgeResident result.2 edge ∧ edge.children = []) ∧
      ∀ edgeKey, (∃ edge ∈ result.1, edge.entry.key = edgeKey) ↔ ∃ row ∈ rows, key row = edgeKey := by
  let result := run (sequence (requests rows)) state
  have after : Coherent result.2 := InternedErasedEdgeReplay.run_coherent _ state (sequence_safe _ (requests_safe rows)) coherent
  have completed := sequence_completed (requests rows) state coherent.valid
  have resultEq : result.1 = rows.map (fun row => (run (makeEdge row.1 row.2 []) result.2).1) := by
    have base : result.1 = (requests rows).map (fun request => (run request result.2).1) := completed.1
    rw [requests, List.map_map] at base
    exact base
  refine ⟨after, ?_, ?_⟩
  · intro edge member
    rw [resultEq] at member
    obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
    have replayed := completed.2 (makeEdge row.1 row.2 []) (List.mem_map.mpr ⟨row, present, rfl⟩)
    have resident := makeEdge_resident row.1 row.2 [] result.2 after
    rw [replayed] at resident
    exact ⟨resident, (nullary_fields row result.2 after).2⟩
  · intro edgeKey
    constructor
    · rintro ⟨edge, member, same⟩
      rw [resultEq] at member
      obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
      exact ⟨row, present, (nullary_fields row result.2 after).1.symm.trans same⟩
    · rintro ⟨row, present, same⟩
      refine ⟨(run (makeEdge row.1 row.2 []) result.2).1, ?_, (nullary_fields row result.2 after).1.trans same⟩
      rw [resultEq]
      exact List.mem_map.mpr ⟨row, present, rfl⟩

/-- Source canonical node construction preserves exactly the declared nullary key set. -/
theorem build_keys [DecidableEq (EdgeKey Symbol Guard)] (rows : List (Symbol × Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state) (edgeKey : EdgeKey Symbol Guard) :
    (∃ edge ∈ nodeEdges (run (build rows) state).1, edge.entry.key = edgeKey) ↔ ∃ row ∈ rows, key row = edgeKey := by
  let output := run (sequence (requests rows)) state
  have checked := completed_rows rows state coherent
  have linkedRows := rows_linked rows state coherent linked
  have survives : surviving output.1 = output.1 := by
    apply List.filter_eq_self.mpr
    intro edge member
    simp only [(checked.2.1 edge member).2, List.any_nil, Bool.not_false]
  rw [build, run_bind, makeNode_edges output.1 output.2 checked.1 linkedRows (fun edge member => (checked.2.1 edge member).1), survives]
  rw [← checked.2.2 edgeKey]
  constructor
  · rintro ⟨edge, member, same⟩
    exact ⟨edge, InternedProbeProvenance.canonicalEdges_member output.1 edge member, same⟩
  · rintro ⟨edge, member, same⟩
    exact ⟨edge, canonicalEdges_retains output.2 checked.1 output.1 edge
      (fun edge member => (checked.2.1 edge member).1) member, same⟩

/-- Read the source symbol and full constraint from a canonical edge record. -/
def declaration (edge : EdgeValue Symbol Guard) : Symbol × Guard := (edge.entry.key.symbol, edge.entry.key.constraint)

/-- Every physical outgoing declaration is exactly an originally requested row. -/
theorem build_declarations [DecidableEq (EdgeKey Symbol Guard)] (rows : List (Symbol × Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (linked : Linked state) (row : Symbol × Guard) :
    row ∈ (nodeEdges (run (build rows) state).1).map declaration ↔ row ∈ rows := by
  constructor
  · intro member
    obtain ⟨edge, present, same⟩ := List.mem_map.mp member
    obtain ⟨original, member, originalKey⟩ := (build_keys rows state coherent linked edge.entry.key).mp ⟨edge, present, rfl⟩
    have fields : original = declaration edge := Prod.ext (congrArg EdgeKey.symbol originalKey) (congrArg EdgeKey.constraint originalKey)
    exact (fields.trans same) ▸ member
  · intro member
    obtain ⟨edge, present, same⟩ := (build_keys rows state coherent linked (key row)).mpr ⟨row, member, rfl⟩
    exact List.mem_map.mpr ⟨edge, present, Prod.ext (congrArg EdgeKey.symbol same) (congrArg EdgeKey.constraint same)⟩

end MicroCFTA.EqualityLeafProjectionNullary
