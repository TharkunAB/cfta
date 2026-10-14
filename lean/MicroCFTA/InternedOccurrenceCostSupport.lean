import MicroCFTA.InternedOccurrenceCostSemantics
import MicroCFTA.InternedDepthFreeProjection

/-!
# Positive support of interpreted occurrence costs

Each interpreted cost names a free reference of the interpreted shape.
A coherent shape with such an occurrence is nonempty. These statements
include nested smart binders and edges with deleted empty children.
-/
namespace MicroCFTA.InternedOccurrenceCostSupport
open InternedNestedConstruction InternedDepthSemantics
open InternedOccurrenceCostSemantics (rename)

/-- Every cost occurrence has a free name in its associated shape. -/
def Supported (shape : Shape Atom) (costs : List (Atom × Nat)) : Prop :=
  ∀ name cost, (name, cost) ∈ costs → name ∈ shape.free

/-- Every lexical slot satisfies positive support, including missing slots. -/
def Inputs (shapes : List (Shape Atom)) (costs : List (List (Atom × Nat))) : Prop :=
  ∀ index : Nat, Supported (shapes[index]?.getD {}) (costs[index]?.getD [])

/-- External renaming preserves positive support without an injectivity premise. -/
theorem rename_supported (function : Atom → Other) (shape : Shape Atom)
    (costs : List (Atom × Nat)) (supported : Supported shape costs) :
    Supported (shape.map function) (rename function costs) := by
  intro name cost member
  obtain ⟨⟨original, prior⟩, present, equal⟩ := List.mem_map.mp member
  cases equal
  rw [InternedDepthFreeProjection.map_free]
  exact List.mem_map.mpr ⟨original, supported original prior present, rfl⟩

/-- Fresh symbolic locals and renamed captures retain positive support. -/
theorem local_inputs (shapes : List (Shape Atom)) (costs : List (List (Atom × Nat)))
    (supported : Inputs shapes costs) :
    Inputs (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr))
      ([(Sum.inl (), 0)] :: costs.map (rename Sum.inr)) := by
  intro index
  cases index with
  | zero => intro name cost member; simpa [Shape.free] using congrArg Prod.fst (List.mem_singleton.mp member)
  | succ index =>
      have mapped := rename_supported (Sum.inr : Atom → Sum Unit Atom) _ _ (supported index)
      cases shapeFound : shapes[index]? <;> cases costFound : costs[index]? <;>
        simpa [List.getElem?_map, shapeFound, costFound, Shape.map, rename] using mapped

mutual
/-- Every full interpreted source cost occurs in the resulting shape's free names. -/
theorem evaluate_supported (expression : Syntax Symbol Guard) (shapes : List (Shape Atom))
    (costs : List (List (Atom × Nat))) (supported : Inputs shapes costs) :
    Supported (evaluate expression shapes) (InternedOccurrenceCostSemantics.evaluate expression shapes costs) := by
  cases expression with
  | empty => intro name cost member; simp [InternedOccurrenceCostSemantics.evaluate] at member
  | var index => simpa only [evaluate, InternedOccurrenceCostSemantics.evaluate] using supported index
  | node edges => simpa only [evaluate, InternedOccurrenceCostSemantics.evaluate] using evaluateEdges_supported edges shapes costs supported
  | union members => simpa only [evaluate, InternedOccurrenceCostSemantics.evaluate] using evaluateMany_supported members shapes costs supported
  | binder smart body =>
      intro name cost member
      rw [InternedOccurrenceCostSemantics.evaluate] at member
      obtain ⟨prior, present, _⟩ := InternedOccurrenceCostSemantics.lower_member _ _ name cost |>.mp member
      have named := evaluate_supported body _ _ (local_inputs shapes costs supported) (.inr name) prior present
      rw [evaluate, InternedDepthFreeProjection.binder_free, InternedFreeNameSemantics.lower_member]
      exact named
termination_by sizeOf expression

/-- Ordered operand costs occur in the combined free names of their shapes. -/
theorem evaluateMany_supported (expressions : List (Syntax Symbol Guard)) (shapes : List (Shape Atom))
    (costs : List (List (Atom × Nat))) (supported : Inputs shapes costs) :
    Supported (combineMany (evaluateMany expressions shapes))
      (InternedOccurrenceCostSemantics.evaluateMany expressions shapes costs) := by
  cases expressions with
  | nil => intro name cost member; simp [InternedOccurrenceCostSemantics.evaluateMany] at member
  | cons first rest =>
      intro name cost member
      rw [evaluateMany, combineMany, InternedDepthFreeProjection.combine_member]
      rw [InternedOccurrenceCostSemantics.evaluateMany] at member
      rcases List.mem_append.mp member with head | tail
      · exact Or.inl (evaluate_supported first shapes costs supported name cost head)
      · exact Or.inr (evaluateMany_supported rest shapes costs supported name cost tail)
termination_by sizeOf expressions

/-- Deleted edges supply no cost, and surviving edges retain every cost's free name. -/
theorem evaluateEdges_supported (expressions : List (EdgeSyntax Symbol Guard)) (shapes : List (Shape Atom))
    (costs : List (List (Atom × Nat))) (supported : Inputs shapes costs) :
    Supported (evaluateEdges expressions shapes)
      (InternedOccurrenceCostSemantics.evaluateEdges expressions shapes costs) := by
  cases expressions with
  | nil => intro name cost member; simp [InternedOccurrenceCostSemantics.evaluateEdges] at member
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          intro name cost member
          rw [evaluateEdges, InternedDepthFreeProjection.combine_member]
          rw [InternedOccurrenceCostSemantics.evaluateEdges] at member
          rcases List.mem_append.mp member with head | tail
          · left
            split at head
            · cases head
            · rename_i live
              simpa [edge, live, Shape.free] using evaluateMany_supported children shapes costs supported name cost head
          · exact Or.inr (evaluateEdges_supported rest shapes costs supported name cost tail)
termination_by sizeOf expressions
end

/-- A coherent shape with a free name cannot be empty. -/
theorem free_nonempty (shape : Shape Atom) (coherent : InternedDepthSemanticProjections.Coherent shape)
    (name : Atom) (member : name ∈ shape.free) : shape.isEmpty = false := by
  cases flag : shape.hasOpaque with
  | true => simp [Shape.isEmpty, flag]
  | false =>
      have deep := coherent flag
      have roots : shape.roots ≠ [] := by intro empty; simp [Shape.free, empty, deep] at member
      simp [Shape.isEmpty, flag, List.isEmpty_eq_false_iff.mpr roots]

/-- A positive interpreted cost prevents empty-child deletion of its result. -/
theorem evaluate_nonempty (expression : Syntax Symbol Guard) (shapes : List (Shape Atom))
    (costs : List (List (Atom × Nat))) (coherent : InternedDepthSemanticProjections.CoherentMany shapes)
    (supported : Inputs shapes costs) (name : Atom) (cost : Nat)
    (member : (name, cost) ∈ InternedOccurrenceCostSemantics.evaluate expression shapes costs) :
    (evaluate expression shapes).isEmpty = false :=
  free_nonempty _ (InternedDepthSemanticProjections.evaluate_coherent expression shapes coherent) name
    (evaluate_supported expression shapes costs supported name cost member)

end MicroCFTA.InternedOccurrenceCostSupport
