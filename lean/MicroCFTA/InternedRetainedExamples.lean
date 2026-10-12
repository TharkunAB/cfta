import MicroCFTA.InternedRetainedCompletion
import MicroCFTA.InternedNestedConstructionReplay

/-!
# Arbitrarily deep source binders with one shared constructor symbol

Each inner body retains every enclosing variable in a live unary edge.
All levels use the same symbol and guard. First completion follows from
fresh-reference provenance rather than constructor-symbol separation.
-/
namespace MicroCFTA.InternedRetainedConstruction
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedNestedCoverage

/-- Retained-reference completion supplies actual record invariants and all subsequent exact replays. -/
theorem closed_complete_record [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (retentive : Retentive 0 expression) :
    ∃ value final, build expression [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build expression [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := closed_completes expression retentive
  have verified := closed_verified expression
  refine ⟨value, final, completed, ?_, closed_covered expression value final completed,
    verified.result value final completed, fun after growth => empty_replay expression value final after completed growth⟩
  simpa only [completed, Outcome.state] using verified.facts

/-- A completed retained-reference input cannot reach an unfinished canonical record. -/
theorem closed_not_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (retentive : Retentive 0 expression) (key : InternedBinderProtocol.NodeKey) (state : State Symbol Guard) :
    build expression [] empty ≠ .pending key state := by
  obtain ⟨value, final, completed⟩ := closed_completes expression retentive
  simp [completed]

/-- Each unary edge reads one enclosing slot after the current local slot. -/
def referenceEdges (indices : List Nat) : List (EdgeSyntax Nat Unit) :=
  indices.map fun index => .mk 0 () [.var (index + 1)]

/-- Every level uses symbol zero while preserving all of its enclosing recursive references. -/
def tower (depth : Nat) : Nat → Syntax Nat Unit
  | 0 => .node [.mk 0 () []]
  | layers + 1 => .binder true (.node (referenceEdges (List.range depth) ++
      [.mk 0 () [.var 0, tower (depth + 1) layers]]))

/-- Ordered edge concatenation preserves both source retention checks. -/
theorem edges_retentive_append (depth : Nat) (left right : List (EdgeSyntax Symbol Guard)) :
    EdgesRetentive depth (left ++ right) ↔ EdgesRetentive depth left ∧ EdgesRetentive depth right := by
  induction left with
  | nil => simp [EdgesRetentive]
  | cons first rest ih =>
      cases first
      simp only [List.cons_append, EdgesRetentive, ih, and_assoc]

/-- Unary variable edges introduce no additional binder dependency requirement. -/
theorem references_retentive (depth : Nat) (indices : List Nat) : EdgesRetentive depth (referenceEdges indices) := by
  induction indices with
  | nil => simp [referenceEdges, EdgesRetentive]
  | cons first rest ih =>
      simpa only [referenceEdges, List.map_cons, EdgesRetentive, ManyRetentive, Retentive, true_and] using ih

/-- Each declared range index has its actual source unary edge. -/
theorem references_declared (depth : Nat) (rest : List (EdgeSyntax Nat Unit)) :
    Declared depth (referenceEdges (List.range depth) ++ rest) := by
  intro index bound
  refine ⟨0, (), List.mem_append_left _ ?_⟩
  exact List.mem_map.mpr ⟨index, List.mem_range.mpr bound, rfl⟩

/-- The retained-reference condition holds at every finite nesting depth without fresh constructor symbols. -/
theorem tower_retentive (depth layers : Nat) : Retentive depth (tower depth layers) := by
  induction layers generalizing depth with
  | zero => simp [tower, Retentive, EdgesRetentive, ManyRetentive]
  | succ layers ih =>
      simp only [tower, Retentive]
      refine ⟨references_declared depth _, edges_retentive_append (depth + 1) _ _ |>.mpr ⟨references_retentive _ _, ?_⟩⟩
      simpa only [EdgesRetentive, ManyRetentive, Retentive, true_and, and_true] using ih (depth + 1)

/-- Source scope checks are preserved by ordered edge concatenation. -/
theorem edges_scoped_append (depth : Nat) (left right : List (EdgeSyntax Symbol Guard)) :
    EdgesScoped depth (left ++ right) ↔ EdgesScoped depth left ∧ EdgesScoped depth right := by
  induction left with
  | nil => simp [EdgesScoped]
  | cons first rest ih =>
      cases first
      simp only [List.cons_append, EdgesScoped, ih, and_assoc]

/-- Every declared unary edge points to an actual enclosing lexical slot. -/
theorem references_scoped (depth : Nat) (indices : List Nat) (bounded : ∀ index ∈ indices, index < depth) :
    EdgesScoped (depth + 1) (referenceEdges indices) := by
  induction indices with
  | nil => simp [referenceEdges, EdgesScoped]
  | cons first rest ih =>
      have firstBound := bounded first List.mem_cons_self
      have tail := ih (fun index member => bounded index (List.mem_cons_of_mem _ member))
      simp only [referenceEdges, List.map_cons, EdgesScoped, ManyScoped, Scoped, and_true]
      exact ⟨Nat.succ_lt_succ firstBound, tail⟩

/-- The entire finite tower closes every variable under its declared source binder. -/
theorem tower_scoped (depth layers : Nat) : Scoped depth (tower depth layers) := by
  induction layers generalizing depth with
  | zero => simp [tower, Scoped, EdgesScoped, ManyScoped]
  | succ layers ih =>
      simp only [tower, Scoped]
      apply (edges_scoped_append _ _ _).mpr
      refine ⟨references_scoped depth (List.range depth) (fun _ member => List.mem_range.mp member), ?_⟩
      simp only [EdgesScoped, ManyScoped, Scoped, and_true]
      exact ⟨Nat.zero_lt_succ depth, ih (depth + 1)⟩

/-- Every finite closed tower completes with full provenance and exact replay, with no first-run success premise. -/
theorem tower_complete (layers : Nat) :
    ∃ value final, build (tower 0 layers) [] empty = .done value final ∧ Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (tower 0 layers) [] after = .done value after :=
  closed_complete_record (tower 0 layers) (tower_retentive 0 layers)

end MicroCFTA.InternedRetainedConstruction
