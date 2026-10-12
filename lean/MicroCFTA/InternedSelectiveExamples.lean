import MicroCFTA.InternedSelectiveCompletion

/-!
# A selective request below arbitrarily many retained source ancestors

Every enclosing binder retains its actual enclosing names. The final
request reads and erases only its immediate parent. It directly retains
all older enclosing names. Every edge uses the same symbol.
-/
namespace MicroCFTA.InternedSelectiveExamples
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedErasureSyntax InternedSelectiveConstruction
open InternedNestedFacts InternedNestedProvenance InternedProbeProvenance InternedNestedCoverage

/-- Direct source edges retain the specified lexical inputs. -/
def vars (indices : List Nat) : List (EdgeSyntax Nat Unit) := indices.map (fun index => .mk 0 () [.var index])

/-- These direct edges contain no nested binder requirement. -/
theorem vars_selective (depth : Nat) (indices : List Nat) : EdgesSelective depth (vars indices) := by
  induction indices with
  | nil => simp [vars, EdgesSelective]
  | cons first rest ih => simpa only [vars, List.map_cons, EdgesSelective, ManySelective, Selective] using And.intro (And.intro trivial trivial) ih

/-- The original direct-edge input list is exact. -/
theorem vars_inputs (indices : List Nat) : edgeInputs (vars indices) = indices := by
  induction indices with
  | nil => simp [vars, edgeInputs]
  | cons first rest ih => simpa [vars, edgeInputs, manyInputs, inputs] using ih

/-- Every declared input has its actual unary source edge. -/
theorem vars_member (index : Nat) (indices : List Nat) (member : index ∈ indices) :
    EdgeSyntax.mk 0 () [.var index] ∈ vars indices := List.mem_map.mpr ⟨index, member, rfl⟩

/-- Appending ordinary source edge lists composes their completion grammar. -/
theorem selective_append (depth : Nat) (left right : List (EdgeSyntax Nat Unit))
    (first : EdgesSelective depth left) (second : EdgesSelective depth right) : EdgesSelective depth (left ++ right) := by
  induction left with
  | nil => exact second
  | cons edge rest ih =>
      cases edge
      simp only [EdgesSelective] at first
      simp only [List.cons_append, EdgesSelective]
      exact ⟨first.1, ih first.2⟩

/-- Appended edge declarations preserve their exact lexical scope. -/
theorem scoped_append (depth : Nat) (left right : List (EdgeSyntax Nat Unit))
    (first : EdgesScoped depth left) (second : EdgesScoped depth right) : EdgesScoped depth (left ++ right) := by
  induction left with
  | nil => exact second
  | cons edge rest ih =>
      cases edge
      simp only [EdgesScoped] at first
      simp only [List.cons_append, EdgesScoped]
      exact ⟨first.1, ih first.2⟩

/-- Each unary source edge reads an actual input when its index is in scope. -/
theorem vars_scoped (depth : Nat) (indices : List Nat) (bounds : ∀ index ∈ indices, index < depth) : EdgesScoped depth (vars indices) := by
  induction indices with
  | nil => simp [vars, EdgesScoped]
  | cons first rest ih =>
      simp only [vars, List.map_cons, EdgesScoped, ManyScoped, Scoped]
      exact ⟨⟨bounds first (by simp), trivial⟩, ih (fun index member => bounds index (by simp [member]))⟩

/-- The live body retains its own local variable and every enclosing input except the nearest parent. -/
def liveIndices (depth : Nat) : List Nat := 0 :: (List.range (depth - 1)).map (fun index => index + 2)

/-- The final body evaluates its nearest parent in a separate discarded edge. -/
def leafBody (depth : Nat) : Syntax Nat Unit := .node
  (vars (liveIndices depth) ++ [.mk 0 () [.var 1, .empty]])

/-- The selected nearest-parent read erases without removing any older declared input. -/
theorem leaf_erased (depth : Nat) : Erased 1 (leafBody depth) := by
  apply Erased.dead
  rw [vars_inputs]
  simp only [liveIndices, List.mem_cons, List.mem_map]
  rintro (impossible | ⟨index, _, same⟩)
  · cases impossible
  · omega

/-- One selective source binder keeps every older ancestor and erases only its immediate parent. -/
def leaf (smart : Bool) (depth : Nat) : Syntax Nat Unit := .binder smart (leafBody depth)

/-- The selective declaration follows from the actual older-variable source edges. -/
theorem leaf_selective (smart : Bool) (depth : Nat) : Selective depth (leaf smart depth) := by
  rw [leaf, leafBody, Selective]
  constructor
  · refine ⟨false, ?_, fun _ => leaf_erased depth⟩
    intro index bound allowed
    have positive : 0 < index := by simpa using allowed
    have member : index + 1 ∈ liveIndices depth := by
      right
      exact List.mem_map.mpr ⟨index - 1, List.mem_range.mpr (by omega), by omega⟩
    exact ⟨0, (), List.mem_append_left _ (vars_member _ _ member)⟩
  · apply selective_append _ _ _ (vars_selective _ _)
    simp [EdgesSelective, ManySelective, Selective]

/-- The selective body has valid local and older-variable reads whenever its immediate parent exists. -/
theorem leaf_scoped (smart : Bool) (depth : Nat) (positive : 0 < depth) : Scoped depth (leaf smart depth) := by
  simp only [leaf, leafBody, Scoped]
  apply scoped_append
  · apply vars_scoped
    intro index member
    simp only [liveIndices, List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨earlier, bound, rfl⟩
    · omega
    · have bound := List.mem_range.mp bound
      omega
  · simp only [EdgesScoped, ManyScoped, Scoped]
    exact ⟨⟨by omega, trivial, trivial⟩, trivial⟩

/-- Each further source layer retains every active input before constructing the next layer. -/
def chain (smart : Bool) (depth : Nat) : Nat → Syntax Nat Unit
  | 0 => leaf smart depth
  | count + 1 => .binder smart (.node
      (vars (List.range (depth + 1)) ++ [.mk 0 () [chain smart (depth + 1) count]]))

/-- Every retained depth admits the final selectively erased request. -/
theorem chain_selective (smart : Bool) (depth count : Nat) : Selective depth (chain smart depth count) := by
  induction count generalizing depth with
  | zero => exact leaf_selective smart depth
  | succ count ih =>
      rw [chain, Selective]
      constructor
      · refine ⟨true, ?_, fun impossible => by cases impossible⟩
        intro index bound allowed
        exact ⟨0, (), List.mem_append_left _ (vars_member (index + 1) _ (List.mem_range.mpr (by omega)))⟩
      · apply selective_append _ _ _ (vars_selective _ _)
        simpa only [EdgesSelective, ManySelective] using And.intro (And.intro (ih (depth + 1)) trivial) trivial

/-- A nonempty enclosing chain supplies every source variable that the selective leaf reads. -/
theorem chain_scoped (smart : Bool) (depth count : Nat) (positive : 0 < depth + count) : Scoped depth (chain smart depth count) := by
  induction count generalizing depth with
  | zero => exact leaf_scoped smart depth (by omega)
  | succ count ih =>
      simp only [chain, Scoped]
      apply scoped_append
      · exact vars_scoped _ _ (fun index member => List.mem_range.mp member)
      · simp only [EdgesScoped, ManyScoped]
        exact ⟨⟨ih (depth + 1) (by omega), trivial⟩, trivial⟩

/-- Two initial retained frames make the final request erase one active ancestor while retaining another. -/
def program (smart : Bool) (count : Nat) : Syntax Nat Unit := chain smart 0 (count + 2)

/-- The unbounded selective family has closed source scope. -/
theorem program_scoped (smart : Bool) (count : Nat) : Scoped 0 (program smart count) := chain_scoped smart 0 (count + 2) (by omega)

/-- The first source execution completes at every raw or smart retained-chain depth. -/
theorem program_complete (smart : Bool) (count : Nat) :
    ∃ value final, build (program smart count) [] empty = .done value final ∧
      Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (program smart count) [] after = .done value after := by
  obtain ⟨value, final, completed⟩ := closed_completes (program smart count) (chain_selective smart 0 (count + 2))
  have verified := closed_verified (program smart count)
  refine ⟨value, final, completed, ?_, closed_covered _ value final completed,
    verified.result value final completed, fun after growth => empty_replay _ value final after completed growth⟩
  simpa only [completed, Outcome.state] using verified.facts

/-- No finite closed selective chain can stop at an unfinished canonical readback. -/
theorem program_not_pending (smart : Bool) (count : Nat) (key : InternedBinderProtocol.NodeKey) (state : State Nat Unit) :
    build (program smart count) [] empty ≠ .pending key state := by
  obtain ⟨value, final, completed, _⟩ := program_complete smart count
  rw [completed]
  intro impossible
  cases impossible

end MicroCFTA.InternedSelectiveExamples
