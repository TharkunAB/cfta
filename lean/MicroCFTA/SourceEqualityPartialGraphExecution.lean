import MicroCFTA.SourceEqualityPartialGraphRunRows

/-!
# Stable actual bounded execution of every completed recursive graph

Mutual graph induction derives a common sufficient bound for traversal and
all native stages. Larger traversal fuel changes recursive callbacks, but
each actual child graph reproduces its identical result and full warm state.
No fixed-callback replay premise or caller termination theorem is assumed.
-/
namespace MicroCFTA.SourceEqualityPartialGraphExecution
open Cache InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialGraph SourceEqualityPartialGraphRuns
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem all_runs :
    (∀ inherited (value : Value Symbol Guard) (before : NativeState width Symbol Guard) result after,
      ReduceNode inherited value before result after → NodeRun inherited value before result after) ∧
    (∀ inherited (edges : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      ReduceRows inherited edges before results after → RowsRun inherited edges before results after) ∧
    (∀ payload (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      ReduceChildren payload values before results after → ChildrenRun payload values before results after) ∧
    (∀ payload index (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      WalkChildren payload index values before results after → WalkRun payload index values before results after) := by
  have emptyCase (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) :
      NodeRun inherited .empty before .empty before := by
    refine ⟨1, ?_⟩
    intro g e p h c n fuel _ _ _ _ _ _ enough
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  have unionCase (inherited : SourceEqualityPrecheck.Constraint) (entry : Interned InternedBinderProtocol.NodeKey)
      (members : List (Value Symbol Guard)) (depth : Nat) (free : List InternedBinderProtocol.Reference) (before : NativeState width Symbol Guard) :
      NodeRun inherited (.union entry members depth free) before (.union entry members depth free) before := by
    refine ⟨1, ?_⟩
    intro g e p h c n fuel _ _ _ _ _ _ enough
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  have nilRows (payload : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) : RowsRun payload [] before [] before :=
    ⟨0, by intros; rfl⟩
  have nilWalk (payload : SourceEqualityPrecheck.Constraint) (index : Nat) (before : NativeState width Symbol Guard) : WalkRun payload index [] before [] before :=
    ⟨0, by intros; rfl⟩
  have contradiction (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) :
      ChildrenRun none values before (values.map (fun _ => .empty)) before := ⟨0, by intros; rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro inherited value before result after trace
    exact ReduceNode.rec
      (motive_1 := fun inherited value before result after _ => NodeRun inherited value before result after)
      (motive_2 := fun inherited edges before results after _ => RowsRun inherited edges before results after)
      (motive_3 := fun payload values before results after _ => ChildrenRun payload values before results after)
      (motive_4 := fun payload index values before results after _ => WalkRun payload index values before results after)
      (fun {inherited before} => emptyCase inherited before)
      (fun {inherited entry members depth free before} => unionCase inherited entry members depth free before)
      (fun {_ _ _ _ _ _ _ _} actual => binder actual)
      (fun {_ _ _ _ _ _ _ _} _ ih => ordinary ih)
      (fun {payload before} => nilRows payload before)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined _ _ childIH restIH => rows_cons narrowed physical combined childIH restIH)
      (fun {values before} => contradiction values before)
      (fun {_ _ _ _ _} _ ih => ih)
      (fun {payload index before} => nilWalk payload index before)
      (fun {_ _ _ _ _ _ _ _ _} _ _ headIH tailIH => walk_cons headIH tailIH) trace
  · intro inherited edges before results after trace
    exact ReduceRows.rec
      (motive_1 := fun inherited value before result after _ => NodeRun inherited value before result after)
      (motive_2 := fun inherited edges before results after _ => RowsRun inherited edges before results after)
      (motive_3 := fun payload values before results after _ => ChildrenRun payload values before results after)
      (motive_4 := fun payload index values before results after _ => WalkRun payload index values before results after)
      (fun {inherited before} => emptyCase inherited before)
      (fun {inherited entry members depth free before} => unionCase inherited entry members depth free before)
      (fun {_ _ _ _ _ _ _ _} actual => binder actual)
      (fun {_ _ _ _ _ _ _ _} _ ih => ordinary ih)
      (fun {payload before} => nilRows payload before)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined _ _ childIH restIH => rows_cons narrowed physical combined childIH restIH)
      (fun {values before} => contradiction values before)
      (fun {_ _ _ _ _} _ ih => ih)
      (fun {payload index before} => nilWalk payload index before)
      (fun {_ _ _ _ _ _ _ _ _} _ _ headIH tailIH => walk_cons headIH tailIH) trace
  · intro payload values before results after trace
    exact ReduceChildren.rec
      (motive_1 := fun inherited value before result after _ => NodeRun inherited value before result after)
      (motive_2 := fun inherited edges before results after _ => RowsRun inherited edges before results after)
      (motive_3 := fun payload values before results after _ => ChildrenRun payload values before results after)
      (motive_4 := fun payload index values before results after _ => WalkRun payload index values before results after)
      (fun {inherited before} => emptyCase inherited before)
      (fun {inherited entry members depth free before} => unionCase inherited entry members depth free before)
      (fun {_ _ _ _ _ _ _ _} actual => binder actual)
      (fun {_ _ _ _ _ _ _ _} _ ih => ordinary ih)
      (fun {payload before} => nilRows payload before)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined _ _ childIH restIH => rows_cons narrowed physical combined childIH restIH)
      (fun {values before} => contradiction values before)
      (fun {_ _ _ _ _} _ ih => ih)
      (fun {payload index before} => nilWalk payload index before)
      (fun {_ _ _ _ _ _ _ _ _} _ _ headIH tailIH => walk_cons headIH tailIH) trace
  · intro payload index values before results after trace
    exact WalkChildren.rec
      (motive_1 := fun inherited value before result after _ => NodeRun inherited value before result after)
      (motive_2 := fun inherited edges before results after _ => RowsRun inherited edges before results after)
      (motive_3 := fun payload values before results after _ => ChildrenRun payload values before results after)
      (motive_4 := fun payload index values before results after _ => WalkRun payload index values before results after)
      (fun {inherited before} => emptyCase inherited before)
      (fun {inherited entry members depth free before} => unionCase inherited entry members depth free before)
      (fun {_ _ _ _ _ _ _ _} actual => binder actual)
      (fun {_ _ _ _ _ _ _ _} _ ih => ordinary ih)
      (fun {payload before} => nilRows payload before)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined _ _ childIH restIH => rows_cons narrowed physical combined childIH restIH)
      (fun {values before} => contradiction values before)
      (fun {_ _ _ _ _} _ ih => ih)
      (fun {payload index before} => nilWalk payload index before)
      (fun {_ _ _ _ _ _ _ _ _} _ _ headIH tailIH => walk_cons headIH tailIH) trace

/-- Every completed node graph has identical bounded execution at all sufficient traversal and native stage bounds. -/
theorem node {inherited value before result after}
    (trace : ReduceNode (width := width) inherited value before result after) : NodeRun inherited value before result after :=
  (all_runs).1 _ _ _ _ _ trace

/-- Ordered rows replay their exact completed results while recursive callbacks change with traversal fuel. -/
theorem rows {inherited edges before results after}
    (trace : ReduceRows (width := width) inherited edges before results after) : RowsRun inherited edges before results after :=
  (all_runs).2.1 _ _ _ _ _ trace

/-- Contradiction and live child adapters both replay at every sufficient bound. -/
theorem children {payload values before results after}
    (trace : ReduceChildren (width := width) payload values before results after) : ChildrenRun payload values before results after :=
  (all_runs).2.2.1 _ _ _ _ _ trace

/-- Indexed child walks replay their actual node results and returned warm states in source order. -/
theorem walk {payload index values before results after}
    (trace : WalkChildren (width := width) payload index values before results after) : WalkRun payload index values before results after :=
  (all_runs).2.2.2 _ _ _ _ _ _ trace

/-- Two complete node graphs at the same actual input have identical returned values and full native states. -/
theorem node_unique {inherited value before first afterFirst second afterSecond}
    (left : ReduceNode (width := width) inherited value before first afterFirst)
    (right : ReduceNode inherited value before second afterSecond) : first = second ∧ afterFirst = afterSecond := by
  obtain ⟨leftBound, leftRun⟩ := node left
  obtain ⟨rightBound, rightRun⟩ := node right
  let bound := max leftBound rightBound
  have firstDone := leftRun bound bound bound bound bound bound bound (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have secondDone := rightRun bound bound bound bound bound bound bound (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have same := SourceEqualityInheritedChildren.Result.done.inj (firstDone.symm.trans secondDone)
  exact ⟨Except.ok.inj same.1, same.2⟩

end MicroCFTA.SourceEqualityPartialGraphExecution
