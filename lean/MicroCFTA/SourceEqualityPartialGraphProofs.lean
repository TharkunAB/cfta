import MicroCFTA.SourceEqualityPartialGraphCases

/-!
# Complete recursive graph preservation without a supplied callback law

Mutual induction follows actual outer nodes, native rows, inherited child
forests, and indexed walks. Each recursive node conclusion comes from its
own child graph. Both physical heaps remain explicit in the input scope.
This theorem does not assert existence of a completed caller graph.
-/
namespace MicroCFTA.SourceEqualityPartialGraphProofs
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityRequiredCache
open SourceEqualityPartialScope SourceEqualityPartialGraph SourceEqualityPartialGraphLaws
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (ambient : InternedGuardedLanguage.Env Symbol)

private theorem all_verified :
    (∀ inherited (value : Value Symbol Guard) (before : NativeState width Symbol Guard) result after,
      ReduceNode inherited value before result after → NodeLaw formulas solver ambient inherited value before result after) ∧
    (∀ inherited (edges : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      ReduceRows inherited edges before results after → RowsLaw formulas solver ambient inherited edges before results after) ∧
    (∀ payload (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      ReduceChildren payload values before results after → ChildrenLaw formulas solver ambient payload values before results after) ∧
    (∀ payload index (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) results after,
      WalkChildren payload index values before results after → WalkLaw formulas solver ambient payload index values before results after) := by
  have nilRows (payload : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) :
      RowsLaw formulas solver ambient payload [] before [] before := by
    intro scope _resident _closed
    exact ⟨scope, pure_keeps _ scope.native.semantic.ready, by simp [Edges], by simp [ClosedEdges], fun _ => ⟨id, fun _ => Iff.rfl⟩⟩
  have nilWalk (payload : SourceEqualityPrecheck.Constraint) (index : Nat) (before : NativeState width Symbol Guard) :
      WalkLaw formulas solver ambient payload index [] before [] before := by
    intro scope _available _closed
    exact ⟨scope, pure_keeps _ scope.native.semantic.ready, by simp [Values], by simp [ClosedValues], fun _ => ⟨id, fun _ => Iff.rfl⟩⟩
  have contradiction (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) :
      ChildrenLaw formulas solver ambient none values before (values.map (fun _ => .empty)) before := by
    intro scope _available _closed _wellFormed
    have erased := SourceEqualityEmptyPropagation.erased_scope before.machine.heap values
    refine ⟨scope, pure_keeps _ scope.native.semantic.ready, erased.1, erased.2, ?_⟩
    intro symbol terms
    constructor
    · intro accepted
      cases values with
      | nil => exact accepted
      | cons value values =>
          cases accepted with
          | cons first _ => simp only [InternedGuardedLanguage.meaning] at first
    · intro impossible; exact False.elim impossible
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro inherited value before result after trace
    exact ReduceNode.rec
      (motive_1 := fun inherited value before result after _ => NodeLaw formulas solver ambient inherited value before result after)
      (motive_2 := fun inherited edges before results after _ => RowsLaw formulas solver ambient inherited edges before results after)
      (motive_3 := fun payload values before results after _ => ChildrenLaw formulas solver ambient payload values before results after)
      (motive_4 := fun payload index values before results after _ => WalkLaw formulas solver ambient payload index values before results after)
      (fun {inherited before} => identity_node formulas solver ambient inherited .empty before)
      (fun {inherited entry members depth free before} => identity_node formulas solver ambient inherited (.union entry members depth free) before)
      (fun {_ _ _ _ _ _ _ _} actual => binder_node formulas solver ambient actual)
      (fun {_ _ _ _ _ _ _ _} _ ih => ordinary_node formulas solver ambient ih)
      (fun {payload before} => nilRows payload before)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined _ _ childIH restIH => rows_cons formulas solver ambient narrowed physical combined childIH restIH)
      (fun {values before} => contradiction values before)
      (fun {_ _ _ _ _} _ ih => live_children formulas solver ambient ih)
      (fun {payload index before} => nilWalk payload index before)
      (fun {_ _ _ _ _ _ _ _ _} _ _ headIH tailIH => walk_cons formulas solver ambient headIH tailIH) trace
  · intro inherited edges before results after trace
    exact ReduceRows.rec
      (motive_1 := fun inherited value before result after _ => NodeLaw formulas solver ambient inherited value before result after)
      (motive_2 := fun inherited edges before results after _ => RowsLaw formulas solver ambient inherited edges before results after)
      (motive_3 := fun payload values before results after _ => ChildrenLaw formulas solver ambient payload values before results after)
      (motive_4 := fun payload index values before results after _ => WalkLaw formulas solver ambient payload index values before results after)
      (fun {inherited before} => identity_node formulas solver ambient inherited .empty before)
      (fun {inherited entry members depth free before} => identity_node formulas solver ambient inherited (.union entry members depth free) before)
      (fun {_ _ _ _ _ _ _ _} actual => binder_node formulas solver ambient actual)
      (fun {_ _ _ _ _ _ _ _} _ ih => ordinary_node formulas solver ambient ih)
      (fun {payload before} => nilRows payload before)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined _ _ childIH restIH => rows_cons formulas solver ambient narrowed physical combined childIH restIH)
      (fun {values before} => contradiction values before)
      (fun {_ _ _ _ _} _ ih => live_children formulas solver ambient ih)
      (fun {payload index before} => nilWalk payload index before)
      (fun {_ _ _ _ _ _ _ _ _} _ _ headIH tailIH => walk_cons formulas solver ambient headIH tailIH) trace
  · intro payload values before results after trace
    exact ReduceChildren.rec
      (motive_1 := fun inherited value before result after _ => NodeLaw formulas solver ambient inherited value before result after)
      (motive_2 := fun inherited edges before results after _ => RowsLaw formulas solver ambient inherited edges before results after)
      (motive_3 := fun payload values before results after _ => ChildrenLaw formulas solver ambient payload values before results after)
      (motive_4 := fun payload index values before results after _ => WalkLaw formulas solver ambient payload index values before results after)
      (fun {inherited before} => identity_node formulas solver ambient inherited .empty before)
      (fun {inherited entry members depth free before} => identity_node formulas solver ambient inherited (.union entry members depth free) before)
      (fun {_ _ _ _ _ _ _ _} actual => binder_node formulas solver ambient actual)
      (fun {_ _ _ _ _ _ _ _} _ ih => ordinary_node formulas solver ambient ih)
      (fun {payload before} => nilRows payload before)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined _ _ childIH restIH => rows_cons formulas solver ambient narrowed physical combined childIH restIH)
      (fun {values before} => contradiction values before)
      (fun {_ _ _ _ _} _ ih => live_children formulas solver ambient ih)
      (fun {payload index before} => nilWalk payload index before)
      (fun {_ _ _ _ _ _ _ _ _} _ _ headIH tailIH => walk_cons formulas solver ambient headIH tailIH) trace
  · intro payload index values before results after trace
    exact WalkChildren.rec
      (motive_1 := fun inherited value before result after _ => NodeLaw formulas solver ambient inherited value before result after)
      (motive_2 := fun inherited edges before results after _ => RowsLaw formulas solver ambient inherited edges before results after)
      (motive_3 := fun payload values before results after _ => ChildrenLaw formulas solver ambient payload values before results after)
      (motive_4 := fun payload index values before results after _ => WalkLaw formulas solver ambient payload index values before results after)
      (fun {inherited before} => identity_node formulas solver ambient inherited .empty before)
      (fun {inherited entry members depth free before} => identity_node formulas solver ambient inherited (.union entry members depth free) before)
      (fun {_ _ _ _ _ _ _ _} actual => binder_node formulas solver ambient actual)
      (fun {_ _ _ _ _ _ _ _} _ ih => ordinary_node formulas solver ambient ih)
      (fun {payload before} => nilRows payload before)
      (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined _ _ childIH restIH => rows_cons formulas solver ambient narrowed physical combined childIH restIH)
      (fun {values before} => contradiction values before)
      (fun {_ _ _ _ _} _ ih => live_children formulas solver ambient ih)
      (fun {payload index before} => nilWalk payload index before)
      (fun {_ _ _ _ _ _ _ _ _} _ _ headIH tailIH => walk_cons formulas solver ambient headIH tailIH) trace

/-- Every actual completed recursive node derives physical scope and exact contextual public meaning. -/
theorem node {inherited value before result after}
    (trace : ReduceNode (width := width) inherited value before result after) :
    NodeLaw formulas solver ambient inherited value before result after :=
  (all_verified formulas solver ambient).1 _ _ _ _ _ trace

/-- Every actual completed ordered row graph derives its physical and public union conclusions. -/
theorem rows {inherited edges before results after}
    (trace : ReduceRows (width := width) inherited edges before results after) :
    RowsLaw formulas solver ambient inherited edges before results after :=
  (all_verified formulas solver ambient).2.1 _ _ _ _ _ trace

/-- Every actual inherited child graph derives its parent-contextual forest conclusion. -/
theorem children {payload values before results after}
    (trace : ReduceChildren (width := width) payload values before results after) :
    ChildrenLaw formulas solver ambient payload values before results after :=
  (all_verified formulas solver ambient).2.2.1 _ _ _ _ _ trace

/-- Every actual indexed child walk derives its pointwise forest conclusion. -/
theorem walk {payload index values before results after}
    (trace : WalkChildren (width := width) payload index values before results after) :
    WalkLaw formulas solver ambient payload index values before results after :=
  (all_verified formulas solver ambient).2.2.2 _ _ _ _ _ _ trace

end MicroCFTA.SourceEqualityPartialGraphProofs
