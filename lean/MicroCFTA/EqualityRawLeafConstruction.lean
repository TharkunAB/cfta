import MicroCFTA.EqualityLeafProjectionNullary
import MicroCFTA.EqualityLeafProjectionLeafCache
import MicroCFTA.SourceNoncanonicalLeafProgress

/-!
# Physical raw nullary rows with source rejection effects

The source evaluates each edge constructor before node normalization. A
rejected row still interns the empty-edge sentinel. The parent removes
that edge, but its allocation and complete cached payload remain.
-/
namespace MicroCFTA.EqualityRawLeafConstruction
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedEdgeResidency InternedFreshProbeKeys EqualityLeafProjectionPhysical
open EqualityLeafProjectionWorkers (sequence sequence_safe sequence_completed)

abbrev ConstraintKey := EqualityLeafProjectionLeafCache.ConstraintKey
noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- The nullary source constructor checks literal Bottom and actual extracted equalities. -/
noncomputable def accepted (guard : Guard Formula) : Bool := by
  classical
  exact decide (guard ≠ .bottom) && EqualityLeafProjectionAdmittedSource.fitsLeaf
    (SourceCompactGuards.sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) guard))

/-- An accepted nullary key retains the original, possibly unnormalized residual. -/
def key (row : Symbol × Guard Formula) : EdgeKey Symbol ConstraintKey := ⟨row.1, [], (some [], row.2)⟩

/-- Rejection uses the actual empty-edge sentinel with one EmptyNode child. -/
def rejectedKey (symbol : Symbol) : EdgeKey Symbol ConstraintKey := ⟨symbol, [.empty], (some [], .top)⟩

/-- Run every source edge request, including rejected rows. -/
noncomputable def request (row : Symbol × Guard Formula) : Work Symbol ConstraintKey (EdgeValue Symbol ConstraintKey) :=
  if accepted row.2 then makeEdge row.1 (some [], row.2) [] else makeEdge row.1 (some [], .top) [.empty]

/-- Complete edge readback retains the requested key before node filtering. -/
theorem edge_key [DecidableEq Symbol] (symbol : Symbol) (constraint : ConstraintKey)
    (children : List (Value Symbol ConstraintKey)) (state : State Symbol ConstraintKey) (coherent : Coherent state) :
    (run (makeEdge symbol constraint children) state).1.entry.key = ⟨symbol, children.map Value.referenceOf, constraint⟩ := by
  let key : EdgeKey Symbol ConstraintKey := ⟨symbol, children.map Value.referenceOf, constraint⟩
  let identify := fun entry => EdgeValue.mk entry children
  have correct := edgeStep_correct key identify state coherent.valid
  have after := edgeStep_coherent key identify state coherent (fun _ same => ⟨rfl, same, rfl⟩)
  exact (after.edges _ _ correct.2.2).2.1

/-- Source deadness reads the exact ordered child references returned from the cache. -/
theorem edge_dead [DecidableEq Symbol] (symbol : Symbol) (constraint : ConstraintKey)
    (children : List (Value Symbol ConstraintKey)) (state : State Symbol ConstraintKey) (coherent : Coherent state) :
    dead (run (makeEdge symbol constraint children) state).1 = children.any (fun child => child.referenceOf == .empty) := by
  have refs := InternedErasedEdgeReplay.makeEdge_references symbol constraint children state coherent
  have same := congrArg (fun values => values.any (fun value => value == InternedBinderProtocol.NodeRef.empty)) refs
  simpa only [dead, List.any_map, Function.comp_def] using same

/-- Rejected source rows have the sentinel key and are exactly the dead parent rows. -/
theorem request_fields [DecidableEq Symbol] (row : Symbol × Guard Formula) (state : State Symbol ConstraintKey)
    (coherent : Coherent state) :
    (run (request row) state).1.entry.key = (if accepted row.2 then key row else rejectedKey row.1) ∧
      dead (run (request row) state).1 = !(accepted row.2) := by
  unfold request
  cases admitted : accepted row.2 <;>
    simp [edge_key, edge_dead, coherent, key, rejectedKey, Value.referenceOf]

/-- Both source edge branches satisfy complete-cache coherence. -/
theorem request_safe (row : Symbol × Guard Formula) : Safe (request row) := by
  unfold request
  split <;> exact makeEdge_safe _ _ _

/-- A row request preserves all pre-existing node-to-edge links. -/
theorem request_linked [DecidableEq Symbol] (row : Symbol × Guard Formula) (state : State Symbol ConstraintKey)
    (coherent : Coherent state) (linked : Linked state) : Linked (run (request row) state).2 := by
  unfold request
  split <;> exact (makeEdge_linked _ _ _ state coherent linked).1

/-- Actual row construction always leaves its complete edge payload resident, including sentinels. -/
theorem request_resident [DecidableEq Symbol] (row : Symbol × Guard Formula) (state : State Symbol ConstraintKey)
    (coherent : Coherent state) : EdgeResident (run (request row) state).2 (run (request row) state).1 := by
  unfold request
  split <;> exact makeEdge_resident _ _ _ state coherent

/-- The row sequence retains source order and every rejected-row effect. -/
noncomputable def requests (rows : List (Symbol × Guard Formula)) := rows.map request

/-- Parent construction removes rejected rows only after every edge request completes. -/
noncomputable def build (rows : List (Symbol × Guard Formula)) : Work Symbol ConstraintKey (Value Symbol ConstraintKey) :=
  (sequence (requests rows)).bind makeNode

theorem requests_safe (rows : List (Symbol × Guard Formula)) : ∀ item ∈ requests rows, Safe item := by
  intro item member
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  exact request_safe row

/-- The completed row sequence preserves physical links. -/
theorem rows_linked [DecidableEq Symbol] (rows : List (Symbol × Guard Formula)) (state : State Symbol ConstraintKey)
    (coherent : Coherent state) (linked : Linked state) : Linked (run (sequence (requests rows)) state).2 := by
  induction rows generalizing state with
  | nil => exact linked
  | cons first rest ih =>
      simp only [requests, List.map_cons, sequence, run_bind, run]
      exact ih _ (InternedErasedEdgeReplay.run_coherent _ state (request_safe first) coherent)
        (request_linked first state coherent linked)

/-- Completed effects derive exact common-cache readback for every raw row occurrence. -/
theorem completed_rows [DecidableEq Symbol] (rows : List (Symbol × Guard Formula)) (state : State Symbol ConstraintKey)
    (coherent : Coherent state) :
    let output := run (sequence (requests rows)) state
    Coherent output.2 ∧ (∀ edge ∈ output.1, EdgeResident output.2 edge) ∧
      output.1 = rows.map (fun row => (run (request row) output.2).1) := by
  let output := run (sequence (requests rows)) state
  have after : Coherent output.2 := InternedErasedEdgeReplay.run_coherent _ state (sequence_safe _ (requests_safe rows)) coherent
  have completed := sequence_completed (requests rows) state coherent.valid
  have same : output.1 = rows.map (fun row => (run (request row) output.2).1) := by
    simpa only [output, requests, List.map_map, Function.comp_def] using completed.1
  refine ⟨after, ?_, same⟩
  intro edge member
  rw [same] at member
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
  have resident := request_resident row output.2 after
  rw [completed.2 (request row) (List.mem_map.mpr ⟨row, present, rfl⟩)] at resident
  exact resident

/-- Canonical node readback contains exactly the accepted original keys and retains raw residual syntax. -/
theorem build_keys [DecidableEq Symbol] (rows : List (Symbol × Guard Formula)) (state : State Symbol ConstraintKey)
    (coherent : Coherent state) (linked : Linked state) (edgeKey : EdgeKey Symbol ConstraintKey) :
    (∃ edge ∈ nodeEdges (run (build rows) state).1, edge.entry.key = edgeKey) ↔
      ∃ row ∈ rows, accepted row.2 = true ∧ key row = edgeKey := by
  let output := run (sequence (requests rows)) state
  have completed := completed_rows rows state coherent
  have linkedRows := rows_linked rows state coherent linked
  rw [build, run_bind, makeNode_edges output.1 output.2 completed.1 linkedRows completed.2.1]
  constructor
  · rintro ⟨edge, present, found⟩
    have original := (normalized_member output.2 completed.1 output.1 completed.2.1 edge).mp present
    rw [completed.2.2] at original
    obtain ⟨row, member, rfl⟩ := List.mem_map.mp original.1
    have fields := request_fields row output.2 completed.1
    have admitted : accepted row.2 = true := by
      have boolean := fields.2.symm.trans original.2
      cases admitted : accepted row.2 <;> simp [admitted] at boolean ⊢
    refine ⟨row, member, admitted, ?_⟩
    simpa only [admitted, Bool.true_eq, ↓reduceIte] using fields.1.symm.trans found
  · rintro ⟨row, member, admitted, same⟩
    let edge := (run (request row) output.2).1
    have fields := request_fields row output.2 completed.1
    refine ⟨edge, (normalized_member output.2 completed.1 output.1 completed.2.1 edge).mpr ⟨?_, ?_⟩, ?_⟩
    · rw [completed.2.2]
      exact List.mem_map.mpr ⟨row, member, rfl⟩
    · simpa only [edge, admitted, Bool.not_true] using fields.2
    · have exactKey : edge.entry.key = key row := by
        simpa only [admitted, Bool.true_eq, ↓reduceIte] using fields.1
      exact exactKey.trans same

/-- The full raw key distinguishes both the constructor and residual syntax. -/
theorem key_injective (first second : Symbol × Guard Formula) (same : key first = key second) : first = second := by
  exact Prod.ext (congrArg EdgeKey.symbol same) (congrArg (fun entry => entry.constraint.2) same)

/-- Raw declaration membership retains duplicate-independent source acceptance. -/
theorem build_member [DecidableEq Symbol] (rows : List (Symbol × Guard Formula))
    (state : State Symbol ConstraintKey) (coherent : Coherent state) (linked : Linked state)
    (row : Symbol × Guard Formula) :
    (∃ edge ∈ nodeEdges (run (build rows) state).1, edge.entry.key = key row) ↔
      row ∈ rows ∧ accepted row.2 = true := by
  rw [build_keys rows state coherent linked]
  constructor
  · rintro ⟨original, member, admitted, same⟩
    have equal := key_injective original row same
    subst original
    exact ⟨member, admitted⟩
  · rintro ⟨member, admitted⟩
    exact ⟨row, member, admitted, rfl⟩

/-- The raw leaf compiler preserves the source constructor invariants. -/
theorem build_safe (rows : List (Symbol × Guard Formula)) : Safe (build rows) :=
  safe_bind _ _ (sequence_safe _ (requests_safe rows)) makeNode_safe

/-- A completed raw leaf has its exact complete record in the actual node cache. -/
theorem build_resident (rows : List (Fin symbols × Guard Formula))
    (state : State (Fin symbols) ConstraintKey) (coherent : Coherent state) :
    Resident (run (build rows) state).2 (run (build rows) state).1 := by
  have rowsCoherent := InternedErasedEdgeReplay.run_coherent _ state
    (sequence_safe _ (requests_safe rows)) coherent
  simp only [build, run_bind]
  exact EqualityLeafProjectionLeafCache.makeNode_resident _ _ rowsCoherent

/-- A finite raw declaration retains its original atom-support certificate. -/
def declarations (rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial)) :
    List (Fin symbols × Guard Formula) := rows.map fun (symbol, row) => (symbol, row.val)

/-- Decode every admitted raw alternative by the exact complete cached edge key. -/
def read (value : Value (Fin symbols) ConstraintKey) :
    NoncanonicalLeafProgress.Node (SourceNoncanonicalLeafProgress.Raw initial) symbols :=
  fun symbol row => ∃ edge ∈ nodeEdges value, edge.entry.key = key (symbol, row.val)

/-- Finite raw construction decodes to precisely its surviving original declarations. -/
theorem build_read (rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (state : State (Fin symbols) ConstraintKey) (coherent : Coherent state) (linked : Linked state) :
    read (run (build (declarations rows)) state).1 =
      fun symbol row => (symbol, row) ∈ rows ∧ accepted row.val = true := by
  funext symbol row
  apply propext
  rw [read, build_keys _ state coherent linked]
  constructor
  · rintro ⟨original, member, admitted, same⟩
    obtain ⟨⟨actual, raw⟩, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨symbolsSame, rowsSame⟩ := Prod.mk.inj (key_injective _ _ same)
    have rawSame : raw = row := Subtype.ext rowsSame
    subst actual
    subst raw
    exact ⟨present, admitted⟩
  · rintro ⟨member, admitted⟩
    exact ⟨(symbol, row.val), List.mem_map.mpr ⟨(symbol, row), member, rfl⟩, admitted, rfl⟩

/-- The source edge check equals the guard and extracted-equality admission proposition. -/
theorem accepted_iff (guard : Guard Formula) : accepted guard = true ↔
    guard ≠ .bottom ∧ EqualityLeafProjectionAdmittedSource.fitsLeaf
      (SourceCompactGuards.sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) guard)) = true := by
  classical
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq]

end MicroCFTA.EqualityRawLeafConstruction
