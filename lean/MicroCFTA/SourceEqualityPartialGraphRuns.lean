import MicroCFTA.SourceEqualityPartialGraphArity

/-!
# Stable bounded execution conclusions for recursive source graphs

A common sufficient bound covers traversal and all six native stages.
Recursive node callbacks change with traversal fuel. These conclusions
require the identical completed values and full native state for every
sufficient bound, so later graph induction can prove that replay directly.
-/
namespace MicroCFTA.SourceEqualityPartialGraphRuns
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Each completed node has an identical source worker result above one sufficient bound. -/
def NodeRun (inherited : SourceEqualityPrecheck.Constraint) (value : Value Symbol Guard) (before : NativeState width Symbol Guard)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard) : Prop :=
  ∃ bound, ∀ g e p h c n fuel, bound ≤ g → bound ≤ e → bound ≤ p → bound ≤ h → bound ≤ c → bound ≤ n → bound ≤ fuel →
    SourceEqualityPartialWorker.run g e p h c n fuel inherited value before = .done (.ok result) after

/-- Actual ordered rows replay while the bounded recursive callback changes. -/
def RowsRun (inherited : SourceEqualityPrecheck.Constraint) (edges : List (EdgeValue Symbol Guard)) (before : NativeState width Symbol Guard)
    (results : List (EdgeValue Symbol Guard)) (after : NativeState width Symbol Guard) : Prop :=
  ∃ bound, ∀ g e p h c n fuel, bound ≤ g → bound ≤ e → bound ≤ p → bound ≤ h → bound ≤ c → bound ≤ n → bound ≤ fuel →
    SourceEqualityInheritedRows.walk (SourceEqualityPartialWorker.run g e p h c n fuel) g e p h c n inherited edges before = .done (.ok results) after

/-- The actual inherited child adapter replays its contradiction or live branch at every sufficient bound. -/
def ChildrenRun (payload : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard) : Prop :=
  ∃ bound, ∀ g e p h c n fuel, bound ≤ g → bound ≤ e → bound ≤ p → bound ≤ h → bound ≤ c → bound ≤ n → bound ≤ fuel →
    SourceEqualityInheritedChildren.run (SourceEqualityPartialWorker.run g e p h c n fuel) payload values before = .done (.ok results) after

/-- Indexed child calls replay each actual recursive result and returned scope in order. -/
def WalkRun (payload : SourceEqualityPrecheck.Constraint) (index : Nat) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard)
    (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard) : Prop :=
  ∃ bound, ∀ g e p h c n fuel, bound ≤ g → bound ≤ e → bound ≤ p → bound ≤ h → bound ≤ c → bound ≤ n → bound ≤ fuel →
    SourceEqualityInheritedChildren.walk (SourceEqualityPartialWorker.run g e p h c n fuel) payload index values before = .done (.ok results) after

/-- The actual Mu request receipt replays without a recursive node request. -/
theorem binder {entry body depth ordinary result heap inherited} {before : NativeState width Symbol Guard}
    (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.machine.heap = .done result heap) :
    NodeRun inherited (.mu entry body depth ordinary) before result (advanceHeap before heap) := by
  refine ⟨1, ?_⟩
  intro g e p h c n fuel _ _ _ _ _ _ enough
  cases fuel with
  | zero => omega
  | succ fuel => simp only [SourceEqualityPartialWorker.run, SourceEqualityPartialWorker.step, actual]

/-- A stable real row graph derives stable ordinary node execution after one traversal entry. -/
theorem ordinary {inherited entry edges results depth free} {before middle : NativeState width Symbol Guard}
    (ih : RowsRun inherited edges before results middle) :
    NodeRun inherited (.node entry edges depth free) before
      (SourceEqualityPartialNodeRebuild.modify (.node entry edges depth free) edges results middle).1
      (SourceEqualityPartialNodeRebuild.modify (.node entry edges depth free) edges results middle).2 := by
  obtain ⟨bound, stable⟩ := ih
  refine ⟨bound + 1, ?_⟩
  intro g e p h c n fuel enoughG enoughE enoughP enoughH enoughC enoughN enoughFuel
  cases fuel with
  | zero => omega
  | succ fuel =>
      have rows := stable g e p h c n fuel (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      simp only [SourceEqualityPartialWorker.run, SourceEqualityPartialWorker.step, rows]

/-- Each actual child and tail graph reproduces its result for the changed recursive callback. -/
theorem walk_cons {payload index value result values results} {before middle after : NativeState width Symbol Guard}
    (headIH : NodeRun (SourceEqualityDescend.descend payload index) value before result middle)
    (tailIH : WalkRun payload (index + 1) values middle results after) :
    WalkRun payload index (value :: values) before (result :: results) after := by
  obtain ⟨headBound, head⟩ := headIH
  obtain ⟨tailBound, tail⟩ := tailIH
  refine ⟨max headBound tailBound, ?_⟩
  intro g e p h c n fuel enoughG enoughE enoughP enoughH enoughC enoughN enoughFuel
  have first := head g e p h c n fuel (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have rest := tail g e p h c n fuel (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [SourceEqualityInheritedChildren.walk, first, SourceEqualityInheritedChildren.Result.bind, rest]

end MicroCFTA.SourceEqualityPartialGraphRuns
