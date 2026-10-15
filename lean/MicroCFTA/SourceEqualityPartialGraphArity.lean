import MicroCFTA.SourceEqualityPartialGraph

/-!
# Arity of completed recursive child and row graphs

The mutual structural proof follows actual contradiction maps and indexed
child walks. Every source setChildren therefore takes its equal-arity direct
interning branch, independently of the language proof.
-/
namespace MicroCFTA.SourceEqualityPartialGraphArity
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph
open SourceEqualityPartialGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem all_lengths :
    (∀ inherited edges (before : NativeState width Symbol Guard) results after,
      ReduceRows inherited edges before results after → results.length = edges.length) ∧
    (∀ payload values (before : NativeState width Symbol Guard) results after,
      ReduceChildren payload values before results after → results.length = values.length) ∧
    (∀ payload index values (before : NativeState width Symbol Guard) results after,
      WalkChildren payload index values before results after → results.length = values.length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro inherited edges before results after trace
    exact ReduceRows.rec
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun _ edges _ results _ _ => results.length = edges.length)
      (motive_3 := fun _ values _ results _ _ => results.length = values.length)
      (motive_4 := fun _ _ values _ results _ _ => results.length = values.length)
      (fun {_ _} => trivial)
      (fun {_ _ _ _ _ _} => trivial)
      (fun {_ _ _ _ _ _ _ _} _ => trivial)
      (fun {_ _ _ _ _ _ _ _} _ _ => trivial)
      (fun {_ _} => rfl)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ restIH => congrArg Nat.succ restIH)
      (fun {_ _} => List.length_map _)
      (fun {_ _ _ _ _} _ ih => ih)
      (fun {_ _ _} => rfl)
      (fun {_ _ _ _ _ _ _ _ _} _ _ _ tailIH => congrArg Nat.succ tailIH) trace
  · intro payload values before results after trace
    exact ReduceChildren.rec
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun _ edges _ results _ _ => results.length = edges.length)
      (motive_3 := fun _ values _ results _ _ => results.length = values.length)
      (motive_4 := fun _ _ values _ results _ _ => results.length = values.length)
      (fun {_ _} => trivial)
      (fun {_ _ _ _ _ _} => trivial)
      (fun {_ _ _ _ _ _ _ _} _ => trivial)
      (fun {_ _ _ _ _ _ _ _} _ _ => trivial)
      (fun {_ _} => rfl)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ restIH => congrArg Nat.succ restIH)
      (fun {_ _} => List.length_map _)
      (fun {_ _ _ _ _} _ ih => ih)
      (fun {_ _ _} => rfl)
      (fun {_ _ _ _ _ _ _ _ _} _ _ _ tailIH => congrArg Nat.succ tailIH) trace
  · intro payload index values before results after trace
    exact WalkChildren.rec
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun _ edges _ results _ _ => results.length = edges.length)
      (motive_3 := fun _ values _ results _ _ => results.length = values.length)
      (motive_4 := fun _ _ values _ results _ _ => results.length = values.length)
      (fun {_ _} => trivial)
      (fun {_ _ _ _ _ _} => trivial)
      (fun {_ _ _ _ _ _ _ _} _ => trivial)
      (fun {_ _ _ _ _ _ _ _} _ _ => trivial)
      (fun {_ _} => rfl)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ restIH => congrArg Nat.succ restIH)
      (fun {_ _} => List.length_map _)
      (fun {_ _ _ _ _} _ ih => ih)
      (fun {_ _ _} => rfl)
      (fun {_ _ _ _ _ _ _ _ _} _ _ _ tailIH => congrArg Nat.succ tailIH) trace

/-- Ordered row processing retains its original row count. -/
theorem rows {inherited edges before results after}
    (trace : ReduceRows (width := width) inherited edges before results after) : results.length = edges.length :=
  (all_lengths).1 _ _ _ _ _ trace

/-- Contradiction and live child traversal retain their original arity. -/
theorem children {payload values before results after}
    (trace : ReduceChildren (width := width) payload values before results after) : results.length = values.length :=
  (all_lengths).2.1 _ _ _ _ _ trace

/-- Indexed source child traversal retains arity at every starting index. -/
theorem walk {payload index values before results after}
    (trace : WalkChildren (width := width) payload index values before results after) : results.length = values.length :=
  (all_lengths).2.2 _ _ _ _ _ _ trace

/-- The actual source child update always uses direct equal-arity interning. -/
theorem setChildren (checked : Symbol → List (Value Symbol Guard) → Guard → Work Symbol Guard (EdgeValue Symbol Guard))
    {payload edge before results after}
    (trace : ReduceChildren (width := width) payload (edge : EdgeValue Symbol Guard).children before results after) :
    EqualityLeafProjectionSetChildren.setChildren checked edge results = makeEdge edge.entry.key.symbol edge.entry.key.constraint results :=
  EqualityLeafProjectionSetChildren.same_arity checked edge results (children trace)

end MicroCFTA.SourceEqualityPartialGraphArity
