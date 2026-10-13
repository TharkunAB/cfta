import MicroCFTA.InternedComputedCompletion
import MicroCFTA.InternedNestedInputScope

/-!
# Recursive construction with computed empty blocking children

The blocking child evaluates another nested binder before node and union
normalization return EmptyNode. Each source layer therefore has real
nested effects before its outer-dependent edge disappears.
-/
namespace MicroCFTA.InternedComputedCompletionExamples
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedComputedEmpty InternedComputedBinderReplay InternedComputedCompletion
open InternedNestedFacts InternedProbeProvenance

/-- Empty union operands include an ordinary node with no edges. -/
def emptyTree : Syntax Nat Unit := .union [.empty, .node []]

/-- Both union operands normalize to EmptyNode. -/
theorem emptyTree_zero : EmptyResult emptyTree := by
  apply EmptyResult.union
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .empty
  · exact .node [] (fun _ _ _ impossible => False.elim (List.not_mem_nil impossible))
      (fun _ _ _ impossible => False.elim (List.not_mem_nil impossible))
      (fun _ _ _ impossible => False.elim (List.not_mem_nil impossible))

/-- The blocking child evaluates its nested source computation before its edge disappears. -/
def blocker (child : Syntax Nat Unit) : Syntax Nat Unit := .node [.mk 0 () [child, emptyTree]]

/-- The actual ordinary normalization returns empty after every successful nested child execution. -/
theorem blocker_zero (child : Syntax Nat Unit) : EmptyResult (blocker child) := by
  refine .node _ (fun _ _ _ _ => emptyTree) ?_ (fun _ _ _ _ => emptyTree_zero)
  intro symbol constraint children member
  have same := List.mem_singleton.mp member
  cases same
  simp

/-- Every further binder computes its blocking child through a deeper nested source call. -/
def tower (smart : Bool) : Nat → Syntax Nat Unit
  | 0 => .var 0
  | count + 1 => .binder smart (.node
      ([.mk 0 () [.var 0]] ++ [.mk 0 () [.var 1, blocker (tower smart count)]]))

/-- The whole call reads only its immediate outer source input. -/
theorem tower_inputs (smart : Bool) (count : Nat) : inputs (tower smart count) = [0] := by
  induction count with
  | zero => simp [tower, inputs]
  | succ count ih => simp [tower, blocker, emptyTree, inputs, edgeInputs, manyInputs, ih, List.filterMap, enclosing]

/-- The computed blocking child erases the enclosing slot structurally while it evaluates its local nested call. -/
theorem blocker_erased (smart : Bool) (count : Nat) : InternedErasureSyntax.Erased 1 (blocker (tower smart count)) := by
  apply InternedErasureSyntax.Erased.unused
  simp [blocker, emptyTree, inputs, edgeInputs, manyInputs, tower_inputs]

/-- Every recursive layer uses the computed-child erasure declaration. -/
theorem tower_admitted (smart : Bool) (count : Nat) : Admitted (tower smart count) := by
  induction count with
  | zero => simp [tower, Admitted]
  | succ count ih =>
      simp only [tower, Admitted]
      constructor
      · exact .computed [.mk 0 () [.var 0]] 0 () (blocker (tower smart count))
          (by simp [edgeInputs, manyInputs, inputs]) (blocker_zero _) (blocker_erased smart count)
      · simp only [List.cons_append, List.nil_append, EdgesAdmitted, ManyAdmitted, Admitted,
          blocker, emptyTree]
        exact ⟨⟨trivial, trivial⟩, ⟨trivial, ⟨⟨ih, ⟨trivial, trivial, trivial⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩

/-- Every actual input read is in lexical scope once the enclosing binder exists. -/
theorem tower_scoped (smart : Bool) (count depth : Nat) (positive : 0 < depth) : Scoped depth (tower smart count) := by
  induction count generalizing depth with
  | zero => simpa [tower, Scoped] using positive
  | succ count ih =>
      have inner := ih (depth + 1) (by omega)
      simp only [tower, blocker, emptyTree, List.cons_append, List.nil_append, Scoped, EdgesScoped, ManyScoped]
      exact ⟨⟨by omega, trivial⟩, ⟨by omega, ⟨⟨inner, ⟨trivial, trivial, trivial⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩

/-- A closed outer binder supplies the source variable used by the whole family. -/
def outerBody (smart : Bool) (count : Nat) : Syntax Nat Unit := .node [.mk 0 () [.var 0, tower smart count]]

/-- The actual outer body admits every finite computed-child recursion depth. -/
theorem outer_admitted (smart : Bool) (count : Nat) : Admitted (outerBody smart count) := by
  simpa only [outerBody, Admitted, EdgesAdmitted, ManyAdmitted] using
    And.intro (And.intro trivial (And.intro (tower_admitted smart count) trivial)) trivial

/-- The source program has no missing lexical input. -/
theorem outer_scoped (smart : Bool) (count : Nat) : Scoped 0 (.binder smart (outerBody smart count)) := by
  simpa only [outerBody, Scoped, EdgesScoped, ManyScoped] using
    And.intro (And.intro (by omega) (And.intro (tower_scoped smart count 1 (by omega)) trivial)) trivial

/-- All source recursion depths complete and derive full record provenance and exact later replay. -/
theorem tower_complete (smart : Bool) (count : Nat) :
    ∃ value final, build (.binder smart (outerBody smart count)) [] empty = .done value final ∧
      Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (.binder smart (outerBody smart count)) [] after = .done value after :=
  closed_complete_record smart (outerBody smart count) (outer_admitted smart count)

/-- Computed-child erasure cannot select an unfinished canonical request in any finite tower. -/
theorem tower_not_pending (smart : Bool) (count : Nat) (key : InternedBinderProtocol.NodeKey) (state : State Nat Unit) :
    build (.binder smart (outerBody smart count)) [] empty ≠ .pending key state := by
  obtain ⟨value, final, completed, _⟩ := tower_complete smart count
  rw [completed]
  intro impossible
  cases impossible

end MicroCFTA.InternedComputedCompletionExamples
