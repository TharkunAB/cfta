import MicroCFTA.SourceEqualityEditWorkerSound
import MicroCFTA.SourceEqualityRequiredWorkerComplete

/-!
# Complete edit graphs execute at every sufficient pair of bounds

Actual leaf equations need no recursive worker bound. Ordinary and recursive
node cases derive their bounds from the finite graph. Child and row scans
retain the exact result and complete returned cache at all larger bounds.
-/
namespace MicroCFTA.SourceEqualityEditWorkerComplete
open InternedConstructorTemplates SourceEqualityEdits
open SourceEqualityEditGraph SourceEqualityRequiredHead SourceEqualityEditWorker
open SourceEqualityRequiredWorker (Result work)
open SourceEqualityRequiredWorkerComplete (StableRun head_stable)

private def NodeStable [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) (needed : Edits Action)
    (value : Value Symbol Guard) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) :=
  StableRun (fun fuel readFuel => edit call fuel readFuel needed value before) result after

private def ChildrenStable [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) (entries : List (Int × Edits Action)) (index : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) :=
  StableRun (fun fuel readFuel => children (edit call fuel readFuel) entries index values before) results after

private def RowsStable [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) (entries : List (Int × Edits Action))
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) :=
  StableRun (fun fuel readFuel => rows (edit call fuel readFuel) entries edges before) results after

private theorem all_stable [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) :
    (∀ (needed : Edits Action) (value : Value Symbol Guard) (before : State Symbol Guard)
      (result : Value Symbol Guard) (after : State Symbol Guard), EditNode (Symbol := Symbol) (Guard := Guard) call needed value before result after →
      NodeStable (Symbol := Symbol) (Guard := Guard) call needed value before result after) ∧
    (∀ (entries : List (Int × Edits Action)) (index : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
      (results : List (Value Symbol Guard)) (after : State Symbol Guard), EditChildren (Symbol := Symbol) (Guard := Guard) call entries index values before results after →
      ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries index values before results after) ∧
    (∀ (entries : List (Int × Edits Action)) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
      (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard), EditRows (Symbol := Symbol) (Guard := Guard) call entries edges before results after →
      RowsStable (Symbol := Symbol) (Guard := Guard) call entries edges before results after) := by
  have leafCase : ∀ {action value before result after},
      call action value before = .done result after →
      NodeStable (Symbol := Symbol) (Guard := Guard) call (.editAt action) value before result after := by
    intro action value before result after actual
    refine ⟨1, 0, ?_⟩
    intro fuel readFuel enough _
    cases fuel with
    | zero => omega
    | succ fuel => exact actual
  have emptyCase : ∀ {entries : List (Int × Edits Action)} {state : State Symbol Guard},
      NodeStable (Symbol := Symbol) (Guard := Guard) call (.editBelow entries) .empty state .empty state := by
    intro entries state
    refine ⟨1, 0, ?_⟩
    intro fuel readFuel enough _
    cases fuel with
    | zero => omega
    | succ fuel => simp only [edit]
  have ordinaryCase : ∀ {entries edges before rebuilt middle value after entry depth free},
      EditRows (Symbol := Symbol) (Guard := Guard) call entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (value, after) → RowsStable (Symbol := Symbol) (Guard := Guard) call entries edges before rebuilt middle →
      NodeStable (Symbol := Symbol) (Guard := Guard) call (.editBelow entries) (.node entry edges depth free) before value after := by
    intro entries edges before rebuilt middle value after entry depth free _ nodeBuilt rowStable
    obtain ⟨bound, headBound, stable⟩ := rowStable
    refine ⟨bound + 1, headBound, ?_⟩
    intro fuel readFuel enough readEnough
    cases fuel with
    | zero => omega
    | succ fuel =>
        have completed := stable fuel readFuel (by omega) readEnough
        simp only [edit, completed, Result.bind, work, nodeBuilt]
  have recursiveCase : ∀ {entries original before exposed middle value after},
      SourceEqualityRequiredGraph.Recursive original → Head original before exposed middle →
      EditNode (Symbol := Symbol) (Guard := Guard) call (.editBelow entries) exposed middle value after → NodeStable (Symbol := Symbol) (Guard := Guard) call (.editBelow entries) exposed middle value after →
      NodeStable (Symbol := Symbol) (Guard := Guard) call (.editBelow entries) original before value after := by
    intro entries original before exposed middle value after recursive headTrace _ bodyStable
    obtain ⟨bound, headBound, stable⟩ := bodyStable
    obtain ⟨readBound, stableHead⟩ := head_stable headTrace
    refine ⟨bound + 1, max headBound readBound, ?_⟩
    intro fuel readFuel enough readEnough
    cases fuel with
    | zero => omega
    | succ fuel =>
        have bodyDone := stable fuel readFuel (by omega) (Nat.le_trans (Nat.le_max_left _ _) readEnough)
        have headDone := stableHead readFuel (Nat.le_trans (Nat.le_max_right _ _) readEnough)
        cases original with
        | empty | reference | node => cases recursive
        | mu | union => simp only [edit, headDone, Result.bind, bodyDone]
  have nilChildren : ∀ {entries index state}, ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries index [] state [] state := by
    intros
    exact ⟨0, 0, fun _ _ _ _ => rfl⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      EditChildren (Symbol := Symbol) (Guard := Guard) call entries (index + 1) values before results after →
      ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries (index + 1) values before results after →
      ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries index (value :: values) before (value :: results) after := by
    intro entries values before results after value index absent _ restStable
    obtain ⟨bound, headBound, stable⟩ := restStable
    refine ⟨bound, headBound, ?_⟩
    intro fuel readFuel enough readEnough
    have completed := stable fuel readFuel enough readEnough
    simp only [children, absent, completed, Result.bind]
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      EditNode (Symbol := Symbol) (Guard := Guard) call needed value before result middle → EditChildren (Symbol := Symbol) (Guard := Guard) call entries (index + 1) values middle results after →
      NodeStable (Symbol := Symbol) (Guard := Guard) call needed value before result middle → ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries (index + 1) values middle results after →
      ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries index (value :: values) before (result :: results) after := by
    intro entries needed value before result middle values results after index found _ _ firstStable restStable
    obtain ⟨firstBound, firstHead, stableFirst⟩ := firstStable
    obtain ⟨restBound, restHead, stableRest⟩ := restStable
    refine ⟨max firstBound restBound, max firstHead restHead, ?_⟩
    intro fuel readFuel enough readEnough
    have firstDone := stableFirst fuel readFuel (Nat.le_trans (Nat.le_max_left _ _) enough)
      (Nat.le_trans (Nat.le_max_left _ _) readEnough)
    have restDone := stableRest fuel readFuel (Nat.le_trans (Nat.le_max_right _ _) enough)
      (Nat.le_trans (Nat.le_max_right _ _) readEnough)
    simp only [children, found, firstDone, restDone, Result.bind]
  have nilRows : ∀ {entries state}, RowsStable (Symbol := Symbol) (Guard := Guard) call entries [] state [] state := by
    intros
    exact ⟨0, 0, fun _ _ _ _ => rfl⟩
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      EditChildren (Symbol := Symbol) (Guard := Guard) call entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      EditRows (Symbol := Symbol) (Guard := Guard) call entries edges afterEdge results after → ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries 0 edge.children before values middle →
      RowsStable (Symbol := Symbol) (Guard := Guard) call entries edges afterEdge results after → RowsStable (Symbol := Symbol) (Guard := Guard) call entries (edge :: edges) before (result :: results) after := by
    intro entries before values middle result afterEdge edges results after edge _ rebuilt _ childStable restStable
    obtain ⟨childBound, childHead, stableChildren⟩ := childStable
    obtain ⟨restBound, restHead, stableRest⟩ := restStable
    refine ⟨max childBound restBound, max childHead restHead, ?_⟩
    intro fuel readFuel enough readEnough
    have childDone := stableChildren fuel readFuel (Nat.le_trans (Nat.le_max_left _ _) enough)
      (Nat.le_trans (Nat.le_max_left _ _) readEnough)
    have restDone := stableRest fuel readFuel (Nat.le_trans (Nat.le_max_right _ _) enough)
      (Nat.le_trans (Nat.le_max_right _ _) readEnough)
    simp only [rows, childDone, Result.bind, work, rebuilt, restDone]
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after trace
    exact EditNode.rec
      (motive_1 := fun needed value before result after _ => NodeStable (Symbol := Symbol) (Guard := Guard) call needed value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries index values before results after)
      (motive_3 := fun entries edges before results after _ => RowsStable (Symbol := Symbol) (Guard := Guard) call entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows keptCase trace
  · intro entries index values before results after trace
    exact EditChildren.rec
      (motive_1 := fun needed value before result after _ => NodeStable (Symbol := Symbol) (Guard := Guard) call needed value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries index values before results after)
      (motive_3 := fun entries edges before results after _ => RowsStable (Symbol := Symbol) (Guard := Guard) call entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows keptCase trace
  · intro entries edges before results after trace
    exact EditRows.rec
      (motive_1 := fun needed value before result after _ => NodeStable (Symbol := Symbol) (Guard := Guard) call needed value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenStable (Symbol := Symbol) (Guard := Guard) call entries index values before results after)
      (motive_3 := fun entries edges before results after _ => RowsStable (Symbol := Symbol) (Guard := Guard) call entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows keptCase trace

/-- Every completed node graph supplies stable complete instrumented execution. -/
theorem node_stable [DecidableEq (EdgeKey Symbol Guard)]
    {call : Callback Action Symbol Guard}
    {needed : Edits Action} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : EditNode (Symbol := Symbol) (Guard := Guard) call needed value before result after) :
    StableRun (fun fuel readFuel => edit call fuel readFuel needed value before) result after :=
  (all_stable call).1 needed value before result after trace

/-- Every finite child graph executes with the same original positions and caches. -/
theorem children_stable [DecidableEq (EdgeKey Symbol Guard)]
    {call : Callback Action Symbol Guard}
    {entries : List (Int × Edits Action)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : EditChildren (Symbol := Symbol) (Guard := Guard) call entries index values before results after) :
    StableRun (fun fuel readFuel => children (edit call fuel readFuel) entries index values before) results after :=
  (all_stable call).2.1 entries index values before results after trace

/-- Every finite row graph retains every original alternative and exact rebuilt edge payloads. -/
theorem rows_stable [DecidableEq (EdgeKey Symbol Guard)]
    {call : Callback Action Symbol Guard}
    {entries : List (Int × Edits Action)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (trace : EditRows (Symbol := Symbol) (Guard := Guard) call entries edges before results after) :
    StableRun (fun fuel readFuel => rows (edit call fuel readFuel) entries edges before) results after :=
  (all_stable call).2.2 entries edges before results after trace

end MicroCFTA.SourceEqualityEditWorkerComplete
