import MicroCFTA.SourceEmptinessClassFoldCosts
import MicroCFTA.SourceEqualityExposureCosts
import MicroCFTA.SourceEmptinessDecision

/-!
# Weighted source records through completed emptiness decisions

Each first task force uses the closed available forest stored in its cell.
Actual row reads retain weighted records before pure task capture. Reached
exploration threads the returned invariant through each force and exposure.
The empty, absent-key, and fixed-point decision branches retain the same
weighted constructor heap. Completed exploration remains an explicit premise.
These receipts use the existing scoped native state and complete row reads.
-/
namespace MicroCFTA.SourceEmptinessDecisionCosts
open InternedConstructorTemplates InternedProbeProvenance
open SourceEmptinessTasks
open SourceEqualityNativeScoped
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Every actual task force retains weighted records at its exact returned native heap. -/
theorem force_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {task : Task Symbol Guard} {before after : State width Symbol Guard} {value : Value Symbol Guard}
    (trace : Force emptyGuard conjoin task before value after) (ready : Ready emptyGuard conjoin before)
    (costs : CostHeap before.native.machine.heap) : CostHeap after.native.machine.heap := by
  cases trace with
  | value => exact costs
  | hit => exact costs
  | miss found _ fold =>
      have original := ready.cells _ _ found
      exact SourceEmptinessClassFoldCosts.fold_costs fold ready.native original.1 original.2.1 costs

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Actual exposure retains weighted records through its row read and effect-free task capture. -/
theorem expose_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {join : Guard → Guard → Guard}
    {value : Value Symbol Guard} {before after : State width Symbol Guard}
    {rows : List (List (Task Symbol Guard))}
    (trace : SourceEmptinessTaskRows.Expose value before rows after) (ready : Ready emptyGuard join before)
    (costs : CostHeap before.native.machine.heap) : CostHeap after.native.machine.heap := by
  cases trace with
  | read available closed actual =>
      rename_i edges heap
      have retained : CostHeap heap := by
        cases actual with
        | done fuel completed =>
            simpa only [completed, MergedSourceExposure.Result.state] using
              (SourceEqualityExposureCosts.nodeEdges_verified fuel value before.native.machine.heap
                ready.native.semantic costs available).costs
      simpa only [SourceEmptinessTaskRows.captureRows_native, advanceNative,
        SourceEqualityNativeScoped.advanceHeap, SourceRecursiveIntersectionThunks.advance] using retained

/-- Every reached exploration trace retains weighted records through each actual local operation. -/
theorem run_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {join : Guard → Guard → Guard}
    (trace : SourceEmptinessTaskTrace.Run (width := width) emptyGuard join budget seen pending before final after)
    (ready : Ready emptyGuard join before) (costs : CostHeap before.native.machine.heap) :
    CostHeap after.native.machine.heap := by
  induction trace with
  | done => exact costs
  | empty forced encoded rest ih =>
      exact ih (forced.effects ready).1 (force_costs forced ready costs)
  | skipped forced encoded skipped rest ih =>
      exact ih (forced.effects ready).1 (force_costs forced ready costs)
  | admit forced encoded fresh exposed rest ih =>
      have first := forced.effects ready
      have firstCosts := force_costs forced ready costs
      exact ih (exposed.effects first.1).1 (expose_costs exposed first.1 firstCosts)

/-- Empty, absent-key, and fixed-point source decisions retain weighted records without a field premise. -/
theorem decision_costs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {answer : Bool} (trace : SourceEmptinessDecision.Decision query before answer after)
    (ready : IdleReady top conjoin before) (costs : CostHeap before.machine.heap) : CostHeap after.machine.heap := by
  cases trace with
  | empty => exact costs
  | missing nonempty actual encoded absent =>
      exact run_costs actual (start_ready before ready) costs
  | known nonempty actual encoded present done answer =>
      exact run_costs actual (start_ready before ready) costs

end MicroCFTA.SourceEmptinessDecisionCosts
