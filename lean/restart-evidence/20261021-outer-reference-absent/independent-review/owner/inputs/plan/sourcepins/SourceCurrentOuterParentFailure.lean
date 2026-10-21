import MicroCFTA.SourceCurrentOuterExecutionAncestry

/-!
# Exact Parent failure dispatch in actual outer execution

A reported Parent fault derives the row entry that invoked its failing
edge call. Earlier siblings contribute their literal completed equations.
No semantic invariant or completed graph is required.
-/
namespace MicroCFTA.SourceCurrentOuterParentFailure
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "run" => SourceCurrentOuterActiveAncestry.run
private theorem erase_failed {actual : Outcome A width}
    (failed : actual.bind (fun _ after => .done () after) = .failed fault after) :
    actual = .failed fault after := by
  cases actual <;> simp_all [Outcome.bind]

private theorem bind_failed (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (failed : first.bind next = .failed fault after) :
    first = .failed fault after ∨ ∃ value middle, first = .done value middle ∧ next value middle = .failed fault after := by
  cases first with
  | failed =>
      simp only [Outcome.bind] at failed
      cases failed
      exact Or.inl rfl
  | done value middle => exact Or.inr ⟨value,middle,rfl,failed⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

private def Dispatch (g s r e p h m c n budget : Nat) (entry : Phase width)
    (observation : SourceCurrentAllocatedParentWorker.Fault width) (after : Caller width) : Prop :=
  ∃ fuel inherited original rest before,
    Reached g s r e p h m c n budget entry (.rows (fuel+1) inherited (original::rest) before) ∧
    edgeCall fuel g s r e p h m c n budget ⟨inherited,original⟩ before = .failed (.parent observation) after

private theorem dispatch_step (first : Step g s r e p h m c n budget entry middle)
    (last : Dispatch g s r e p h m c n budget middle observation after) :
    Dispatch g s r e p h m c n budget entry observation after := by
  obtain ⟨fuel,inherited,original,rest,before,later,failed⟩ := last
  exact ⟨fuel,inherited,original,rest,before,(Reached.snoc (.refl _) first).trans later,failed⟩

private def NodeFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget request (before : Caller width) observation after,
  nodeCall fuel g s r e p h m c n budget request before = .failed (.parent observation) after →
  Dispatch g s r e p h m c n budget (.node fuel request before) observation after
private def BodyFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget request (before : Caller width) observation after,
  nodeBody fuel g s r e p h m c n budget request before = .failed (.parent observation) after →
  Dispatch g s r e p h m c n budget (.body fuel request before) observation after
private def RowsFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited values (before : Caller width) observation after,
  rows fuel g s r e p h m c n budget inherited values before = .failed (.parent observation) after →
  Dispatch g s r e p h m c n budget (.rows fuel inherited values before) observation after
private def DescendantsFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited value (before : Caller width) observation after,
  descendants fuel g s r e p h m c n budget inherited value before = .failed (.parent observation) after →
  Dispatch g s r e p h m c n budget (.descendants fuel inherited value before) observation after
private def ChildrenFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget combined values (before : Caller width) observation after,
  children fuel g s r e p h m c n budget combined values before = .failed (.parent observation) after →
  Dispatch g s r e p h m c n budget (.children fuel combined values before) observation after
private def WalkFailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget combined index values (before : Caller width) observation after,
  walk fuel g s r e p h m c n budget combined index values before = .failed (.parent observation) after →
  Dispatch g s r e p h m c n budget (.walk fuel combined index values before) observation after

private theorem all_failures (fuel : Nat) :
    NodeFailureAt (width := width) fuel ∧ BodyFailureAt (width := width) fuel ∧ RowsFailureAt (width := width) fuel ∧
      DescendantsFailureAt (width := width) fuel ∧ ChildrenFailureAt (width := width) fuel ∧ WalkFailureAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget combined index values before observation after failed
      cases values with
      | nil => simp only [walk] at failed; cases failed
      | cons value rest =>
        cases fuel with
        | zero => simp only [walk] at failed; cases failed
        | succ fuel =>
          simp only [walk] at failed
          rcases bind_failed _ _ failed with headFailed | ⟨head,middle,headDone,later⟩
          · exact dispatch_step .walk_head ((ih fuel (Nat.lt_succ_self _)).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ headFailed)
          · rcases bind_failed _ _ later with tailFailed | ⟨outputs,final,tailDone,impossible⟩
            · exact dispatch_step (.walk_tail headDone)
                ((ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  tailFailed)
            · cases impossible
    have childrenAt : ChildrenFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget combined values before observation after failed
      cases combined with
      | contradiction => simp only [children] at failed; cases failed
      | live identity records =>
        simp only [children] at failed
        exact dispatch_step (.children_walk (by intro impossible; cases impossible))
          (walkAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ failed)
    have descendantsAt : DescendantsFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before observation after failed
      simp only [descendants] at failed
      split at failed
      · cases failed
      · cases failed
      · rename_i combined observed
        rcases bind_failed _ _ failed with childFailed | ⟨outputs,middle,childDone,impossible⟩
        · have observed : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).1 =
              .ok (some combined) := observed
          have prefixEq : advance before
              (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
                ⟨before.checked.native.machine.heap,
                  (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).2⟩)
              before.fourth before.merge = SourceCurrentAllocatedPartialGraph.prefixState before value inherited := rfl
          rw [prefixEq] at childFailed
          exact dispatch_step (.descendants_children observed) (childrenAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ childFailed)
        · cases impossible
    have rowsAt : RowsFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before observation after failed
      cases values with
      | nil => simp only [rows] at failed; cases failed
      | cons original rest =>
        cases fuel with
        | zero => simp only [rows] at failed; cases failed
        | succ fuel =>
          simp only [rows] at failed
          rcases bind_failed _ _ failed with edgeFailed | ⟨narrowed,middle,edgeDone,later⟩
          · exact ⟨fuel,inherited,original,rest,before,.refl _,edgeFailed⟩
          · rcases bind_failed _ _ later with childFailed | ⟨result,returned,childDone,suffix⟩
            · exact dispatch_step (.rows_edge edgeDone)
                ((ih fuel (Nat.lt_succ_self _)).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  childFailed)
            · rcases bind_failed _ _ suffix with tailFailed | ⟨outputs,final,tailDone,impossible⟩
              · exact dispatch_step (.rows_tail edgeDone childDone)
                  ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tailFailed)
              · cases impossible
    have bodyAt : BodyFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget request before observation after failed
      rcases request with ⟨inherited,value⟩
      cases value with
      | empty | union | reference => simp only [nodeBody] at failed; cases failed
      | mu entry body depth ordinary =>
        simp only [nodeBody] at failed
        split at failed <;> cases failed
      | node entry original depth free =>
        cases fuel with
        | zero => simp only [nodeBody] at failed; cases failed
        | succ fuel =>
          simp only [nodeBody] at failed
          rcases bind_failed _ _ failed with rowsFailed | ⟨outputs,middle,rowsDone,impossible⟩
          · exact dispatch_step (.body_rows rfl)
              ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rowsFailed)
          · cases impossible
    have nodeAt : NodeFailureAt (width := width) fuel := by
      intro g s r e p h m c n budget request before observation after failed
      rcases started : beginNode request before with ⟨chosen,action,running⟩
      cases action with
      | ready result | absent | busy => simp only [nodeCall,started] at failed; cases failed
      | evaluate original =>
        simp only [nodeCall,started] at failed
        rcases bind_failed _ _ failed with bodyFailed | ⟨result,middle,bodyDone,impossible⟩
        · exact dispatch_step (.node_evaluate started)
            (bodyAt _ _ _ _ _ _ _ _ _ _ _ _ _ _ bodyFailed)
        · cases impossible
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

/-- Every reported Parent fault derives its exact failing edge call and preceding literal prefix. -/
theorem failed {g s r e p h m c n budget : Nat} {phase : Phase width}
    {observation : SourceCurrentAllocatedParentWorker.Fault width} {after : Caller width}
    (actual : run g s r e p h m c n budget phase = .failed (.parent observation) after) :
    ∃ fuel inherited original rest before,
      Reached g s r e p h m c n budget phase (.rows (fuel+1) inherited (original::rest) before) ∧
      edgeCall fuel g s r e p h m c n budget ⟨inherited,original⟩ before = .failed (.parent observation) after := by
  cases phase with
  | node fuel request before => exact (all_failures fuel).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed actual)
  | body fuel request before => exact (all_failures fuel).2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed actual)
  | rows fuel inherited values before => exact (all_failures fuel).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed actual)
  | descendants fuel inherited value before => exact (all_failures fuel).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed actual)
  | children fuel combined values before => exact (all_failures fuel).2.2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed actual)
  | walk fuel combined index values before => exact (all_failures fuel).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed actual)

end MicroCFTA.SourceCurrentOuterParentFailure
