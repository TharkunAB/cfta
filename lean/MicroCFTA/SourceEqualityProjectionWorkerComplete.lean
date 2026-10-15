import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceEqualityRequiredWorkerComplete

/-!
# Stable finite execution of every complete path graph

The graph supplies both proof bounds. Every larger pair returns the same
value and full constructor cache. No initial cache premise is needed here.
-/
namespace MicroCFTA.SourceEqualityProjectionWorkerComplete
open InternedConstructorTemplates SourceEqualityProjectionGraph SourceEqualityProjectionWorker
open SourceEqualityRequiredWorker (Result work)
open SourceEqualityRequiredWorkerComplete (StableRun head_stable)

/-- A completed row read remains complete with identical effects at every larger bound. -/
theorem read_stable [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : SourceEqualityProjectionRead.Read value before edges after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges after := by
  cases trace with
  | done bound completed =>
      refine ⟨bound, ?_⟩
      intro fuel enough
      have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable bound (fuel - bound) value before
        (by simp only [completed, MergedSourceExposure.Finished])
      rw [show bound + (fuel - bound) = fuel by omega] at stable
      exact stable.trans completed

/-- Every finite ordered union scan has one sufficient row-read bound. -/
theorem readAll_stable [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : SourceEqualityProjectionUnion.ReadAll values before edges after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → readAll fuel values before = .done edges after := by
  induction trace with
  | nil => exact ⟨0, by intros; rfl⟩
  | cons first rest ih =>
      obtain ⟨firstBound, firstStable⟩ := read_stable first
      obtain ⟨restBound, restStable⟩ := ih
      refine ⟨max firstBound restBound, ?_⟩
      intro fuel enough
      simp only [readAll, firstStable fuel (Nat.le_trans (Nat.le_max_left _ _) enough),
        restStable fuel (Nat.le_trans (Nat.le_max_right _ _) enough), Result.bind]

/-- Every completed source union has stable full constructor effects. -/
theorem union_stable [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (trace : SourceEqualityProjectionUnion.Union values before result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → union fuel values before = .done result after := by
  cases trace with
  | node read built =>
      obtain ⟨bound, stable⟩ := readAll_stable read
      exact ⟨bound, by intro fuel enough; simp only [union, stable fuel enough, Result.bind, work, built]⟩

private def NodeStable [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) :=
  StableRun (fun fuel readFuel => project fuel readFuel path value before) result after

private def RowsStable [DecidableEq (EdgeKey Symbol Guard)] (path : List Int) (index : Int)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (after : State Symbol Guard) :=
  StableRun (fun fuel readFuel => rows (project fuel readFuel path) index edges before) results after

private theorem stable [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodeStable path value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsStable path index edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeStable [] value state value state := by
    intro value state
    refine ⟨1, 0, ?_⟩
    intro fuel readFuel enough _
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  have emptyCase : ∀ {index path state}, NodeStable (index :: path) (.empty : Value Symbol Guard) state .empty state := by
    intro index path state
    refine ⟨1, 0, ?_⟩
    intro fuel readFuel enough _
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsStable path index edges before values middle →
      NodeStable (index :: path) (.node entry edges depth free) before result after := by
    intro path index edges before values middle result after entry depth free _ unionTrace rowsIH
    obtain ⟨workerBound, readBound, rowsStable⟩ := rowsIH
    obtain ⟨unionBound, unionStable⟩ := union_stable unionTrace
    refine ⟨workerBound + 1, max readBound unionBound, ?_⟩
    intro fuel readFuel enough readEnough
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp only [project, rowsStable fuel readFuel (by omega) (Nat.le_trans (Nat.le_max_left _ _) readEnough),
          Result.bind, unionStable readFuel (Nat.le_trans (Nat.le_max_right _ _) readEnough)]
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeStable (index :: path) exposed middle result after → NodeStable (index :: path) original before result after := by
    intro original before exposed middle path index result after recursive head _ bodyIH
    obtain ⟨workerBound, readBound, bodyStable⟩ := bodyIH
    obtain ⟨headBound, headStable⟩ := head_stable head
    refine ⟨workerBound + 1, max readBound headBound, ?_⟩
    intro fuel readFuel enough readEnough
    cases fuel with
    | zero => omega
    | succ fuel =>
        have first := headStable readFuel (Nat.le_trans (Nat.le_max_right _ _) readEnough)
        have body := bodyStable fuel readFuel (by omega) (Nat.le_trans (Nat.le_max_left _ _) readEnough)
        cases original with
        | empty | reference | node => cases recursive
        | union | mu => simp only [project, first, Result.bind, body]
  have nilCase : ∀ {path index state}, RowsStable path index ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intros; exact ⟨0, 0, by intros; rfl⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsStable path index edges before results after → RowsStable path index (edge :: edges) before results after := by
    intro edge path index edges before results after absent _ ih
    obtain ⟨bound, readBound, stable⟩ := ih
    exact ⟨bound, readBound, by intro fuel readFuel enough readEnough; simpa only [rows, absent] using stable fuel readFuel enough readEnough⟩
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeStable path child before result middle →
      RowsStable path index edges middle results after → RowsStable path index (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found _ _ firstIH restIH
    obtain ⟨firstBound, firstRead, firstStable⟩ := firstIH
    obtain ⟨restBound, restRead, restStable⟩ := restIH
    refine ⟨max firstBound restBound, max firstRead restRead, ?_⟩
    intro fuel readFuel enough readEnough
    simp only [rows, found, firstStable fuel readFuel (Nat.le_trans (Nat.le_max_left _ _) enough)
      (Nat.le_trans (Nat.le_max_left _ _) readEnough), Result.bind,
      restStable fuel readFuel (Nat.le_trans (Nat.le_max_right _ _) enough) (Nat.le_trans (Nat.le_max_right _ _) readEnough)]
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun path value before result after _ => NodeStable path value before result after)
      (motive_2 := fun path index edges before results after _ => RowsStable path index edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun path value before result after _ => NodeStable path value before result after)
      (motive_2 := fun path index edges before results after _ => RowsStable path index edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every completed physical getPath graph executes at all sufficient proof bounds. -/
theorem node_stable [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) : NodeStable path value before result after := stable.1 _ _ _ _ _ trace

/-- Every completed physical forest projection executes at all sufficient proof bounds. -/
theorem forest_stable [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) : StableRun (fun fuel readFuel => forest fuel readFuel path values before) result after := by
  cases trace with
  | root unionTrace =>
      obtain ⟨bound, stable⟩ := union_stable unionTrace
      exact ⟨0, bound, by intro fuel readFuel _ enough; exact stable readFuel enough⟩
  | missing absent => exact ⟨0, 0, by intros; simp only [forest, absent]⟩
  | selected found body =>
      obtain ⟨bound, readBound, stable⟩ := node_stable body
      exact ⟨bound, readBound, by intro fuel readFuel enough readEnough; simpa only [forest, found] using stable fuel readFuel enough readEnough⟩

end MicroCFTA.SourceEqualityProjectionWorkerComplete
