import MicroCFTA.InternedDeepErasureCompletion

/-!
# Closed towers erase parent and grandparent reads below nested binders

The discarded dependencies sit inside live child nodes. Each binder body
also has a root self union. Every layer reads both enclosing names before
normalization removes those reads. One shared symbol suffices at all depths.
-/
namespace MicroCFTA.InternedDeepErasureExamples
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedErasureSyntax InternedDeepErasureCompletion
open InternedNestedFacts InternedProbeProvenance

/-- A live constant alternative survives beside an evaluated outer-dependent discarded edge. -/
def leaf (slot : Nat) : Syntax Nat Unit := .node [.mk 0 () [], .mk 0 () [.var slot, .empty]]

/-- Each leaf reads its designated original lexical slot. -/
theorem leaf_inputs (slot : Nat) : inputs (leaf slot) = [slot] := by
  simp [leaf, inputs, edgeInputs, manyInputs]

/-- The original designated read erases, and every other slot is unused. -/
theorem leaf_erased (slot index : Nat) : Erased index (leaf slot) := by
  by_cases same : index = slot
  · subst index
    exact .dead slot [.mk 0 () []] 0 () (by simp [edgeInputs, manyInputs])
  · exact .unused index (leaf slot) (by simp [leaf_inputs, same])

/-- Leaves contain no nested binder and need no further completion premise. -/
theorem leaf_admitted (slot : Nat) : Admitted (leaf slot) := by
  simp [leaf, Admitted, EdgesAdmitted, ManyAdmitted]

/-- Each new layer contains a deeper binder, local recursion, and erased parent and grandparent reads. -/
def tower (smart : Bool) : Nat → Syntax Nat Unit
  | 0 => .node [.mk 0 () []]
  | count + 1 => .binder smart (.union [.var 0,
      .node [.mk 0 () [.var 0, tower smart count, leaf 1, leaf 2]]])

/-- The live nested call really reads its grandparent's original lexical slot. -/
theorem tower_reads_grandparent (smart : Bool) (count : Nat) : 1 ∈ inputs (tower smart (count + 1)) := by
  rw [tower, inputs]
  apply List.mem_filterMap.mpr
  refine ⟨2, ?_, rfl⟩
  simp [inputs, manyInputs, edgeInputs, leaf_inputs]

/-- The source root self union lies outside the earlier root-node erasure grammar. -/
theorem outside_previous (smart : Bool) (count : Nat) :
    ¬ InternedRecursiveErasure.Admitted (tower smart (count + 1)) := by
  simp [tower, InternedRecursiveErasure.Admitted]

/-- The body erases every selected outer slot through its actual child declarations. -/
theorem body_erased (smart : Bool) (count index : Nat)
    (nested : Erased (index + 1) (tower smart count)) :
    Erased (index + 1) (.union [.var 0, .node [.mk 0 () [.var 0, tower smart count, leaf 1, leaf 2]]]) := by
  apply Erased.union
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .unused _ _ (by simp [inputs])
  · apply Erased.node
    intro symbol constraint children member selected included
    have same : EdgeSyntax.mk symbol constraint children = EdgeSyntax.mk 0 () [.var 0, tower smart count, leaf 1, leaf 2] := by simpa using member
    cases same
    simp only [List.mem_cons, List.not_mem_nil, or_false] at included
    rcases included with rfl | rfl | rfl | rfl
    · exact .unused _ _ (by simp [inputs])
    · exact nested
    · exact leaf_erased 1 _
    · exact leaf_erased 2 _

/-- Every selected external dependency erases through all intervening nested source constructors. -/
theorem tower_erased (smart : Bool) (count index : Nat) : Erased index (tower smart count) := by
  induction count generalizing index with
  | zero => exact .unused index _ (by simp [tower, inputs, edgeInputs, manyInputs])
  | succ count ih =>
      rw [tower]
      exact .binder index smart _ (body_erased smart count index (ih (index + 1)))

/-- First construction admits every finite depth of actual nested dependency erasure. -/
theorem tower_admitted (smart : Bool) (count : Nat) : Admitted (tower smart count) := by
  induction count with
  | zero => simp [tower, Admitted, EdgesAdmitted, ManyAdmitted]
  | succ count ih =>
      rw [tower, Admitted]
      refine ⟨body_erased smart count 0 (tower_erased smart count 1), ?_⟩
      simp only [Admitted, ManyAdmitted, EdgesAdmitted]
      exact ⟨trivial, ⟨⟨⟨trivial, ih, leaf_admitted 1, leaf_admitted 2, trivial⟩, trivial⟩, trivial⟩⟩

/-- A leaf is scoped when its actual declared input exists. -/
theorem leaf_scoped (slot depth : Nat) (bound : slot < depth) : Scoped depth (leaf slot) := by
  simp only [leaf, Scoped, EdgesScoped, ManyScoped]
  exact ⟨trivial, ⟨bound, trivial, trivial⟩, trivial⟩

/-- Two enclosing variables suffice at every nested depth. -/
theorem tower_scoped (smart : Bool) (count depth : Nat) (enough : 2 ≤ depth) : Scoped depth (tower smart count) := by
  induction count generalizing depth with
  | zero => simp [tower, Scoped, EdgesScoped, ManyScoped]
  | succ count ih =>
      simp only [tower, Scoped, ManyScoped, EdgesScoped]
      exact ⟨by omega, ⟨⟨⟨by omega, ih (depth + 1) (by omega), leaf_scoped 1 _ (by omega),
        leaf_scoped 2 _ (by omega), trivial⟩, trivial⟩, trivial⟩⟩

/-- The middle binder supplies the second variable that the inner tower reads. -/
def middle (smart : Bool) (count : Nat) : Syntax Nat Unit :=
  .binder smart (.node [.mk 0 () [.var 0, tower smart count]])

/-- The middle body's original outer dependency erases only below its nested live child. -/
theorem middle_erased (smart : Bool) (count : Nat) :
    Erased 1 (.node [.mk 0 () [.var 0, tower smart count]]) := by
  apply Erased.node
  intro symbol constraint children member child included
  have same : EdgeSyntax.mk symbol constraint children = EdgeSyntax.mk 0 () [.var 0, tower smart count] := by simpa using member
  cases same
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl
  · exact .unused _ _ (by simp [inputs])
  · exact tower_erased smart count 1

/-- The middle binder has derived erasure and recursively admitted source children. -/
theorem middle_admitted (smart : Bool) (count : Nat) : Admitted (middle smart count) := by
  simp only [middle, Admitted, EdgesAdmitted, ManyAdmitted]
  exact ⟨middle_erased smart count, ⟨⟨trivial, tower_admitted smart count, trivial⟩, trivial⟩⟩

/-- The complete outer body supplies both enclosing variables before the nested tower runs. -/
def outerBody (smart : Bool) (count : Nat) : Syntax Nat Unit := .node [.mk 0 () [.var 0, middle smart count]]

/-- Every inner source computation satisfies the derived first-run completion grammar. -/
theorem outer_admitted (smart : Bool) (count : Nat) : Admitted (outerBody smart count) := by
  simp only [outerBody, Admitted, EdgesAdmitted, ManyAdmitted]
  exact ⟨⟨trivial, middle_admitted smart count, trivial⟩, trivial⟩

/-- The whole family is closed lexical source syntax. -/
theorem outer_scoped (smart : Bool) (count : Nat) : Scoped 0 (.binder smart (outerBody smart count)) := by
  simp only [outerBody, middle, Scoped, EdgesScoped, ManyScoped]
  exact ⟨⟨by omega, ⟨⟨by omega, tower_scoped smart count 2 (by omega), trivial⟩, trivial⟩, trivial⟩, trivial⟩

/-- Both raw and smart source towers complete at every finite depth with complete records and exact later replay. -/
theorem tower_complete (smart : Bool) (count : Nat) :
    ∃ value final, build (.binder smart (outerBody smart count)) [] empty = .done value final ∧
      Facts final ∧ Covered [] final ∧ Available final value ∧
      ∀ after, Grows final after → build (.binder smart (outerBody smart count)) [] after = .done value after :=
  closed_complete_record smart (outerBody smart count) (outer_admitted smart count)

/-- Every finite closed tower avoids unfinished canonical readback on its first source execution. -/
theorem tower_not_pending (smart : Bool) (count : Nat) (key : InternedBinderProtocol.NodeKey) (state : State Nat Unit) :
    build (.binder smart (outerBody smart count)) [] empty ≠ .pending key state := by
  obtain ⟨value, final, completed, _⟩ := tower_complete smart count
  rw [completed]
  intro impossible
  cases impossible

end MicroCFTA.InternedDeepErasureExamples
