import MicroCFTA.SourceEqualityRequiredWorkerSound

/-!
# Every physical required-path graph executes at all sufficient bounds

The proof derives separate worker and head-read bounds from the finite graph.
Larger bounds retain both the exact result and the complete final cache.
Each intermediate constructor equation remains the actual source request.
-/
namespace MicroCFTA.SourceEqualityRequiredWorkerComplete
open InternedConstructorTemplates SourceEqualityNeeded
open SourceEqualityRequiredGraph SourceEqualityRequiredHead SourceEqualityRequiredWorker

/-- A finite pair of bounds suffices for every larger worker and head-read budget. -/
def StableRun (evaluation : Nat → Nat → Result Symbol Guard A) (result : A) (after : State Symbol Guard) : Prop :=
  ∃ workerBound headBound, ∀ workerFuel headFuel, workerBound ≤ workerFuel → headBound ≤ headFuel →
    evaluation workerFuel headFuel = .done result after

/-- The actual head receipt supplies a stable finite bound for exposure and reconstruction. -/
theorem head_stable [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard} (trace : Head value before result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → head fuel value before = .done result after := by
  cases trace with
  | read bound edges middle exposed rebuilt =>
      refine ⟨bound, ?_⟩
      intro fuel enough
      have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable bound (fuel - bound) value before
        (by simp only [exposed, MergedSourceExposure.Finished])
      rw [show bound + (fuel - bound) = fuel by omega] at stable
      have completed := stable.trans exposed
      simp only [head, completed, work, rebuilt]


private def NodeStable [DecidableEq (EdgeKey Symbol Guard)] (needed : Needed)
    (value : Value Symbol Guard) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) :=
  StableRun (fun fuel readFuel => require fuel readFuel needed value before) result after

private def ChildrenStable [DecidableEq (EdgeKey Symbol Guard)] (entries : List (Int × Needed)) (index : Nat)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) :=
  StableRun (fun fuel readFuel => children (require fuel readFuel) entries index values before) results after

private def RowsStable [DecidableEq (EdgeKey Symbol Guard)] (entries : List (Int × Needed))
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) :=
  StableRun (fun fuel readFuel => rows (require fuel readFuel) entries edges before) results after

private theorem all_stable [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ (needed : Needed) (value : Value Symbol Guard) (before : State Symbol Guard)
      (result : Value Symbol Guard) (after : State Symbol Guard), RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result after →
      NodeStable (Symbol := Symbol) (Guard := Guard) needed value before result after) ∧
    (∀ (entries : List (Int × Needed)) (index : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
      (results : List (Value Symbol Guard)) (after : State Symbol Guard), RequireChildren (Symbol := Symbol) (Guard := Guard) entries index values before results after →
      ChildrenStable (Symbol := Symbol) (Guard := Guard) entries index values before results after) ∧
    (∀ (entries : List (Int × Needed)) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
      (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard), RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after →
      RowsStable (Symbol := Symbol) (Guard := Guard) entries edges before results after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state : State Symbol Guard},
      NodeStable (Symbol := Symbol) (Guard := Guard) (.node []) value state value state := by
    intro value state
    refine ⟨1, 0, ?_⟩
    intro fuel readFuel enough _
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  have emptyCase : ∀ {entries : List (Int × Needed)} {state : State Symbol Guard}, entries ≠ [] →
      NodeStable (Symbol := Symbol) (Guard := Guard) (.node entries) .empty state .empty state := by
    intro entries state nonempty
    refine ⟨1, 0, ?_⟩
    intro fuel readFuel enough _
    cases fuel with
    | zero => omega
    | succ fuel => simp only [require, List.isEmpty_iff, nonempty, ite_false]
  have ordinaryCase : ∀ {entries edges before rebuilt middle value after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (value, after) → RowsStable (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      NodeStable (Symbol := Symbol) (Guard := Guard) (.node entries) (.node entry edges depth free) before value after := by
    intro entries edges before rebuilt middle value after entry depth free nonempty _ nodeBuilt rowStable
    obtain ⟨bound, headBound, stable⟩ := rowStable
    refine ⟨bound + 1, headBound, ?_⟩
    intro fuel readFuel enough readEnough
    cases fuel with
    | zero => omega
    | succ fuel =>
        have completed := stable fuel readFuel (by omega) readEnough
        simp only [require, List.isEmpty_iff, nonempty, ite_false, completed, Result.bind, work, nodeBuilt]
  have recursiveCase : ∀ {entries original before exposed middle value after},
      entries ≠ [] → Recursive original → Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle value after → NodeStable (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle value after →
      NodeStable (Symbol := Symbol) (Guard := Guard) (.node entries) original before value after := by
    intro entries original before exposed middle value after nonempty recursive headTrace _ bodyStable
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
        | mu | union => simp only [require, List.isEmpty_iff, nonempty, ite_false, headDone, Result.bind, bodyDone]
  have nilChildren : ∀ {entries index state}, ChildrenStable (Symbol := Symbol) (Guard := Guard) entries index [] state [] state := by
    intros
    exact ⟨0, 0, fun _ _ _ _ => rfl⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenStable (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenStable (Symbol := Symbol) (Guard := Guard) entries index (value :: values) before (value :: results) after := by
    intro entries values before results after value index absent _ restStable
    obtain ⟨bound, headBound, stable⟩ := restStable
    refine ⟨bound, headBound, ?_⟩
    intro fuel readFuel enough readEnough
    have completed := stable fuel readFuel enough readEnough
    simp only [children, absent, completed, Result.bind]
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle → RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeStable (Symbol := Symbol) (Guard := Guard) needed value before result middle → ChildrenStable (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      ChildrenStable (Symbol := Symbol) (Guard := Guard) entries index (value :: values) before (result :: results) after := by
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
  have nilRows : ∀ {entries state}, RowsStable (Symbol := Symbol) (Guard := Guard) entries [] state [] state := by
    intros
    exact ⟨0, 0, fun _ _ _ _ => rfl⟩
  have rejectedCase : ∀ {entries edges before results after edge},
      fits (.node entries) edge.children.length = false → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after →
      RowsStable (Symbol := Symbol) (Guard := Guard) entries edges before results after → RowsStable (Symbol := Symbol) (Guard := Guard) entries (edge :: edges) before results after := by
    intro entries edges before results after edge doesNotFit _ restStable
    obtain ⟨bound, headBound, stable⟩ := restStable
    refine ⟨bound, headBound, ?_⟩
    intro fuel readFuel enough readEnough
    have completed := stable fuel readFuel enough readEnough
    simp only [rows, doesNotFit, Bool.false_eq_true, ite_false, completed]
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      fits (.node entries) edge.children.length = true → RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after → ChildrenStable (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      RowsStable (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after → RowsStable (Symbol := Symbol) (Guard := Guard) entries (edge :: edges) before (result :: results) after := by
    intro entries before values middle result afterEdge edges results after edge doesFit _ rebuilt _ childStable restStable
    obtain ⟨childBound, childHead, stableChildren⟩ := childStable
    obtain ⟨restBound, restHead, stableRest⟩ := restStable
    refine ⟨max childBound restBound, max childHead restHead, ?_⟩
    intro fuel readFuel enough readEnough
    have childDone := stableChildren fuel readFuel (Nat.le_trans (Nat.le_max_left _ _) enough)
      (Nat.le_trans (Nat.le_max_left _ _) readEnough)
    have restDone := stableRest fuel readFuel (Nat.le_trans (Nat.le_max_right _ _) enough)
      (Nat.le_trans (Nat.le_max_right _ _) readEnough)
    simp only [rows, doesFit, ite_true, childDone, Result.bind, work, rebuilt, restDone]
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after trace
    exact RequireNode.rec
      (motive_1 := fun needed value before result after _ => NodeStable (Symbol := Symbol) (Guard := Guard) needed value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenStable (Symbol := Symbol) (Guard := Guard) entries index values before results after)
      (motive_3 := fun entries edges before results after _ => RowsStable (Symbol := Symbol) (Guard := Guard) entries edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows rejectedCase keptCase trace
  · intro entries index values before results after trace
    exact RequireChildren.rec
      (motive_1 := fun needed value before result after _ => NodeStable (Symbol := Symbol) (Guard := Guard) needed value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenStable (Symbol := Symbol) (Guard := Guard) entries index values before results after)
      (motive_3 := fun entries edges before results after _ => RowsStable (Symbol := Symbol) (Guard := Guard) entries edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows rejectedCase keptCase trace
  · intro entries edges before results after trace
    exact RequireRows.rec
      (motive_1 := fun needed value before result after _ => NodeStable (Symbol := Symbol) (Guard := Guard) needed value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenStable (Symbol := Symbol) (Guard := Guard) entries index values before results after)
      (motive_3 := fun entries edges before results after _ => RowsStable (Symbol := Symbol) (Guard := Guard) entries edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows rejectedCase keptCase trace

/-- Every completed node graph supplies stable complete instrumented execution. -/
theorem node_stable [DecidableEq (EdgeKey Symbol Guard)]
    {needed : Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result after) :
    StableRun (fun fuel readFuel => require fuel readFuel needed value before) result after :=
  all_stable.1 needed value before result after trace

/-- Every finite child graph executes with the same original positions and caches. -/
theorem children_stable [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireChildren (Symbol := Symbol) (Guard := Guard) entries index values before results after) :
    StableRun (fun fuel readFuel => children (require fuel readFuel) entries index values before) results after :=
  all_stable.2.1 entries index values before results after trace

/-- Every finite row graph retains its rejection order and exact rebuilt edge payloads. -/
theorem rows_stable [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after) :
    StableRun (fun fuel readFuel => rows (require fuel readFuel) entries edges before) results after :=
  all_stable.2.2 entries edges before results after trace

end MicroCFTA.SourceEqualityRequiredWorkerComplete
