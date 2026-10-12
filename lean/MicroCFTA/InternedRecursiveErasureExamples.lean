import MicroCFTA.InternedRecursiveErasure
import MicroCFTA.InternedNestedInputScope

/-!
# Arbitrary-depth closed erased-dependency examples

Every nested binder reads its parent in a discarded edge. All edges use
the same symbol. Live children retain their own local reference and the
next nested binder. Both raw and smart construction use the same proof.
-/
namespace MicroCFTA.InternedRecursiveErasureExamples
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedRecursiveErasure InternedNestedErasureReplay InternedNestedDependencies
open InternedNestedFacts InternedProbeProvenance

/-- Each further source layer erases its immediate parent's reference after evaluating a deeper layer. -/
def tower (smart : Bool) : Nat → Syntax Nat Unit
  | 0 => .var 0
  | count + 1 => .binder smart (body [.mk 0 () [.var 0, tower smart count]] 0 ())

/-- Each whole nested call syntactically reads exactly its immediate outer input. -/
theorem tower_inputs (smart : Bool) (count : Nat) : inputs (tower smart count) = [0] := by
  induction count with
  | zero => simp [tower, inputs]
  | succ count ih => simp [tower, body, inputs, edgeInputs, manyInputs, ih, List.filterMap, enclosing]

/-- All depths satisfy the recursive erased-dependency grammar. -/
theorem tower_admitted (smart : Bool) (count : Nat) : Admitted (tower smart count) := by
  induction count with
  | zero => simp [tower, Admitted]
  | succ count ih =>
      rw [tower, body, Admitted]
      refine ⟨⟨[.mk 0 () [.var 0, tower smart count]], 0, (), rfl, ?_⟩, ?_⟩
      · simp [edgeInputs, manyInputs, inputs, tower_inputs]
      · simp only [List.cons_append, List.nil_append, EdgesAdmitted, ManyAdmitted, Admitted]
        exact ⟨⟨trivial, ih, trivial⟩, ⟨trivial, trivial, trivial⟩, trivial⟩

/-- Each layer is lexically scoped when its actual enclosing variable exists. -/
theorem tower_scoped (smart : Bool) (count depth : Nat) (positive : 0 < depth) : Scoped depth (tower smart count) := by
  induction count generalizing depth with
  | zero => simpa [tower, Scoped] using positive
  | succ count ih =>
      have inner := ih (depth + 1) (by omega)
      simp only [tower, body, List.cons_append, List.nil_append, Scoped, EdgesScoped, ManyScoped]
      exact ⟨⟨by omega, inner, trivial⟩, ⟨by omega, trivial, trivial⟩, trivial⟩

/-- A complete outer body supplies the local variable used by the entire nested family. -/
def outerBody (smart : Bool) (count : Nat) : Syntax Nat Unit :=
  .node [.mk 0 () [.var 0, tower smart count]]

/-- The outer body permits every recursively erased inner depth. -/
theorem outer_admitted (smart : Bool) (count : Nat) : Admitted (outerBody smart count) := by
  simpa only [outerBody, Admitted, EdgesAdmitted, ManyAdmitted] using
    And.intro (And.intro trivial (And.intro (tower_admitted smart count) trivial)) trivial

/-- The complete family has no missing lexical inputs. -/
theorem outer_scoped (smart : Bool) (count : Nat) : Scoped 0 (.binder smart (outerBody smart count)) := by
  simpa only [outerBody, Scoped, EdgesScoped, ManyScoped] using
    And.intro (And.intro (by omega) (And.intro (tower_scoped smart count 1 (by omega)) trivial)) trivial

/-- Every finite raw or smart tower completes from empty tables and produces a fully available canonical record. -/
theorem tower_complete (smart : Bool) (count : Nat) :
    ∃ value final, build (.binder smart (outerBody smart count)) [] empty = .done value final ∧
      Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (.binder smart (outerBody smart count)) [] after = .done value after :=
  closed_complete_record smart (outerBody smart count) (outer_admitted smart count)

/-- No depth in the closed family can stop on an unfinished canonical request. -/
theorem tower_not_pending (smart : Bool) (count : Nat) (key : InternedBinderProtocol.NodeKey) (state : State Nat Unit) :
    build (.binder smart (outerBody smart count)) [] empty ≠ .pending key state := by
  obtain ⟨value, final, completed, _⟩ := tower_complete smart count
  rw [completed]
  intro impossible
  cases impossible

end MicroCFTA.InternedRecursiveErasureExamples
