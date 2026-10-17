import MicroCFTA.SourceCurrentUnionNormalProjectionGate
import MicroCFTA.SourceCurrentAllocatedConjunctionWorker

/-!
# Union normality through actual conjunction exploration

Every demanded exposure and projection retains the invariant. Equality
folds change only operations. The proof includes every finite worklist
branch and every stopping result of the allocated fourth-memo request.
-/
namespace MicroCFTA.SourceCurrentUnionNormalConjunction
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)

private theorem bind (first : SourceCurrentConjunctionRowsWorker.Outcome Symbol Formula A)
    (next : A → SourceCurrentConjunctionRowsWorker.Physical Symbol Formula → SourceCurrentConjunctionRowsWorker.Outcome Symbol Formula B)
    (normal : UnionNormal first.state.heap)
    (later : ∀ value after, UnionNormal after.heap → UnionNormal (next value after).state.heap) :
    UnionNormal (first.bind next).state.heap := by
  cases first with
  | failed => exact normal
  | done value state => exact later value state normal

private theorem exposures [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] (reader : Nat)
    (values : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))
    (state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentConjunctionRowsWorker.exposures reader values state).state.heap := by
  induction values generalizing state with
  | nil => exact normal
  | cons value rest ih =>
      have retained := SourceCurrentRequiredUnionNormalRead.nodeEdges reader value state.heap normal
      cases actual : MergedFreshOrdinaryExposure.nodeEdges reader value state.heap with
      | done rows after =>
          have afterNormal : UnionNormal after := by simpa only [actual,MergedSourceExposure.Result.state] using retained
          rw [SourceCurrentConjunctionRowsWorker.exposures,actual]
          exact bind _ _ (ih ⟨after,state.equality⟩ afterNormal) (fun _ _ currentNormal => currentNormal)
      | pending | unresolved | exhausted =>
          simpa only [SourceCurrentConjunctionRowsWorker.exposures,actual,SourceCurrentConjunctionRowsWorker.Outcome.state,
            MergedSourceExposure.Result.state] using retained

private theorem projections [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] (worker reader : Nat)
    (jobs : List (SourceCurrentConjunctionRowsWorker.Job Symbol Formula))
    (state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentConjunctionRowsWorker.projections worker reader jobs state).state.heap := by
  induction jobs generalizing state with
  | nil => exact normal
  | cons job rest ih =>
      rcases job with ⟨values,path⟩
      have retained := SourceCurrentUnionNormalProjectionGate.forest worker reader (path.map Int.ofNat) values state.heap normal
      cases actual : SourceEqualityProjectionWorker.forest worker reader (path.map Int.ofNat) values state.heap with
      | done value after =>
          have afterNormal : UnionNormal after := by simpa only [actual,SourceCurrentRequiredUnionNormalRead.StoppedNormal] using retained
          rw [SourceCurrentConjunctionRowsWorker.projections,actual]
          exact bind _ _ (ih ⟨after,state.equality⟩ afterNormal) (fun _ _ currentNormal => currentNormal)
      | pending | unresolved | exhausted =>
          simpa only [SourceCurrentConjunctionRowsWorker.projections,actual,SourceCurrentConjunctionRowsWorker.Outcome.state,
            SourceCurrentRequiredUnionNormalRead.StoppedNormal] using retained

private theorem classes [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] (worker reader : Nat)
    (forests : List (List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))) (constraints : EqualityNormalize.Constraints)
    (state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentConjunctionRowsWorker.classes worker reader forests constraints state).state.heap := by
  induction constraints generalizing state with
  | nil => exact normal
  | cons paths rest ih => exact bind _ _ (projections worker reader _ state normal) (fun _ middle middleNormal =>
      bind _ _ (ih middle middleNormal) (fun _ _ currentNormal => currentNormal))

private theorem requirements [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] (worker reader : Nat)
    (edges : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))) (constraints : EqualityNormalize.Constraints)
    (state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentConjunctionRowsWorker.requirements worker reader edges constraints state).state.heap :=
  bind _ _ (classes worker reader _ constraints state normal) (fun _ _ currentNormal => currentNormal)

private theorem tuple [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] (worker reader : Nat)
    (edges : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)))
    (state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentConjunctionRowsWorker.tuple worker reader edges state).state.heap := by
  unfold SourceCurrentConjunctionRowsWorker.tuple
  dsimp only
  split
  · exact normal
  · exact normal
  · split
    · exact normal
    · exact bind _ _ (requirements worker reader edges _ _ normal) (fun _ _ currentNormal => currentNormal)

private theorem tuples [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] (worker reader : Nat)
    (edges : List (List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))))
    (state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentConjunctionRowsWorker.tuples worker reader edges state).state.heap := by
  induction edges generalizing state with
  | nil => exact normal
  | cons edge rest ih => exact bind _ _ (tuple worker reader edge state normal) (fun _ middle middleNormal =>
      bind _ _ (ih middle middleNormal) (fun _ _ currentNormal => currentNormal))

private theorem rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
    (worker reader : Nat) (values : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))
    (state : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentConjunctionRowsWorker.rows worker reader values state).state.heap :=
  bind _ _ (exposures reader values state normal) (fun _ after afterNormal => tuples worker reader _ after afterNormal)

private theorem explore [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
    (worker reader budget : Nat) (table : SourceCurrentConjunctionWorker.Table Symbol Formula)
    (pending : List (List (Value Symbol (SourceSymbolicIndex.Constraint Formula))))
    (state : SourceCurrentConjunctionWorker.Physical Symbol Formula) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentConjunctionWorker.explore worker reader budget table pending state).state.heap := by
  induction budget using Nat.strongRecOn generalizing table pending state with
  | ind budget lower =>
      induction pending generalizing table state with
      | nil => simpa only [SourceCurrentConjunctionWorker.explore,SourceCurrentConjunctionWorker.Outcome.state] using normal
      | cons values rest tail =>
          rw [SourceCurrentConjunctionWorker.explore]
          split
          · exact tail table state normal
          · split
            · exact tail table state normal
            · rename_i admitted
              have positive := (SourceCurrentConjunctionEmptinessTable.admitted SourceCurrentConjunctionRequirements.key
                SourceCurrentConjunctionWorklist.closed budget table values (Bool.eq_false_iff.mpr admitted)).1
              have retained := rows worker reader values state normal
              cases actual : SourceCurrentConjunctionRowsWorker.rows worker reader values state with
              | done requirements after =>
                  have afterNormal : UnionNormal after.heap := by simpa only [actual,SourceCurrentConjunctionRowsWorker.Outcome.state] using retained
                  exact lower (budget-1) (by omega) _ _ after afterNormal
              | failed fault after =>
                  simpa only [actual,SourceCurrentConjunctionRowsWorker.Outcome.state,SourceCurrentConjunctionWorker.Outcome.state] using retained

private theorem decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
    [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))] (worker reader budget : Nat)
    (value : Value Symbol (SourceSymbolicIndex.Constraint Formula))
    (state : SourceCurrentConjunctionWorker.Physical Symbol Formula) (normal : UnionNormal state.heap) :
    UnionNormal (SourceCurrentConjunctionWorker.decision worker reader budget value state).state.heap := by
  unfold SourceCurrentConjunctionWorker.decision
  split
  · have retained := explore worker reader budget [] [[value]] state normal
    cases actual : SourceCurrentConjunctionWorker.explore worker reader budget [] [[value]] state with
    | failed => simpa only [actual,SourceCurrentConjunctionWorker.Outcome.bind,SourceCurrentConjunctionWorker.Outcome.state] using retained
    | done table after =>
        have afterNormal : UnionNormal after.heap := by simpa only [actual,SourceCurrentConjunctionWorker.Outcome.state] using retained
        simp only [SourceCurrentConjunctionWorker.Outcome.bind]
        split <;> exact afterNormal
  · exact normal

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Actual fourth-memo decisions retain normality on misses, hits, and failures. -/
theorem call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (worker reader budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (query : Value Symbol Guard)
    (before : SourceEqualityNativeDemand.State width) (normal : UnionNormal before.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedConjunctionWorker.call worker reader budget query before memo).state.native.machine.heap := by
  have retained : UnionNormal (SourceCurrentConjunctionWorker.call worker reader budget memo query
      (SourceCurrentAllocatedNativeEffects.physical before)).state.heap := by
    unfold SourceCurrentConjunctionWorker.call
    split
    · exact normal
    · have checked := decision worker reader budget query (SourceCurrentAllocatedNativeEffects.physical before) normal
      cases actual : SourceCurrentConjunctionWorker.decision worker reader budget query (SourceCurrentAllocatedNativeEffects.physical before) <;>
        simpa only [actual,SourceCurrentConjunctionWorker.Outcome.bind,SourceCurrentConjunctionWorker.Outcome.state] using checked
  cases actual : SourceCurrentConjunctionWorker.call worker reader budget memo query
      (SourceCurrentAllocatedNativeEffects.physical before) <;>
    simpa only [SourceCurrentAllocatedConjunctionWorker.call,actual,SourceCurrentAllocatedConjunctionWorker.Outcome.state,
      SourceCurrentConjunctionWorker.Outcome.state,SourceCurrentAllocatedQueryMemo.advancePhysical,SourceRecursiveIntersectionThunks.advance] using retained
end MicroCFTA.SourceCurrentUnionNormalConjunction
