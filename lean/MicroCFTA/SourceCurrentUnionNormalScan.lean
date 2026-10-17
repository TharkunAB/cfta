import MicroCFTA.SourceCurrentUnionNormalTargets
import MicroCFTA.SourceCurrentUnionNormalConjunction
import MicroCFTA.SourceCurrentAllocatedRecordScanWorker

/-!
# Union normality through literal current Scan

Primary and secondary gates retain their distinct endpoint rules. Refused
classes execute the actual first-seeded query and fourth memo. Selection,
skips, stopped classes, failed prefixes, and ordered suffixes are included.
-/
namespace MicroCFTA.SourceCurrentUnionNormalScan
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

private theorem gate_lift (tag : InternedNestedConstruction.Outcome Symbol Guard (Option Bool) → SourceCurrentAllocatedGateWorker.Fault)
    (before : Checked width) (actual : InternedNestedConstruction.Outcome Symbol Guard (Option Bool))
    (normal : UnionNormal actual.state) :
    UnionNormal (SourceCurrentAllocatedGateWorker.lift tag before actual).state.native.machine.heap := by
  cases actual with
  | pending => exact normal
  | done answer state => cases answer <;> exact normal

private theorem gate [DecidableEq (EdgeKey Symbol Guard)]
    (below : Bool) (fuel : Nat) (values : List (Value Symbol Guard)) (paths : EqualityNormalize.Class)
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedScanWorker.gate below fuel values paths state memo).state.native.machine.heap := by
  have checked : UnionNormal (if below then SourceCurrentAllocatedGateWorker.primary fuel values paths state
      else SourceCurrentAllocatedGateWorker.secondary fuel values paths state).state.native.machine.heap := by
    cases below
    · exact gate_lift _ _ _ (SourceCurrentUnionNormalProjectionGate.gate false source reaches fuel values paths _ normal)
    · exact gate_lift _ _ _ (SourceCurrentUnionNormalProjectionGate.gate true source reaches fuel values paths _ normal)
  cases actual : (if below then SourceCurrentAllocatedGateWorker.primary fuel values paths state
      else SourceCurrentAllocatedGateWorker.secondary fuel values paths state) <;>
    simpa only [SourceCurrentAllocatedScanWorker.gate,actual,SourceCurrentAllocatedScanWorker.Outcome.state,
      SourceCurrentAllocatedGateWorker.Outcome.state] using checked

private theorem query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (p h n : Nat) (values : List (Value Symbol Guard)) (paths : EqualityNormalize.Class)
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedScanWorker.query p h n values paths state memo).state.native.machine.heap := by
  have retained := SourceCurrentUnionNormalTargets.seeded p h n values (paths.map (List.map Int.ofNat)) state normal
  cases actual : SourceCurrentAllocatedSeededWorker.seeded p h n values (paths.map (List.map Int.ofNat)) state <;>
    simpa only [SourceCurrentAllocatedScanWorker.query,actual,SourceCurrentAllocatedScanWorker.Outcome.state,
      SourceCurrentAllocatedSeededWorker.Outcome.state] using retained

private theorem decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (p h budget : Nat) (paths : EqualityNormalize.Class) (value : Value Symbol Guard)
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedScanWorker.decision p h budget paths value state memo).state.native.machine.heap := by
  have retained := SourceCurrentUnionNormalConjunction.call p h budget memo value state normal
  cases actual : SourceCurrentAllocatedConjunctionWorker.call p h budget value state memo <;>
    simpa only [SourceCurrentAllocatedScanWorker.decision,actual,SourceCurrentAllocatedScanWorker.Outcome.state,
      SourceCurrentAllocatedConjunctionWorker.Outcome.state] using retained

private theorem bind (first : SourceCurrentAllocatedScanWorker.Outcome A width)
    (next : A → Checked width → Memo → SourceCurrentAllocatedScanWorker.Outcome B width)
    (normal : UnionNormal first.state.native.machine.heap)
    (later : ∀ value after memo, UnionNormal after.native.machine.heap → UnionNormal (next value after memo).state.native.machine.heap) :
    UnionNormal (first.bind next).state.native.machine.heap := by
  cases first with
  | failed => exact normal
  | done value state memo => exact later value state memo normal

private theorem select_state (paths : EqualityNormalize.Class)
    (first : SourceCurrentAllocatedScanWorker.Outcome SourceCurrentAllocatedScanWorker.Result width) :
    (first.select paths).state = first.state := by
  cases first with
  | failed => rfl
  | done value => cases value; rfl

/-- Every actual bounded path Scan retains normality at its exact stopping state. -/
theorem scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (g s p h n budget : Nat) (values : List (Value Symbol Guard)) (paths : EqualityNormalize.Constraints)
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedScanWorker.scan g s p h n budget values paths state memo).state.native.machine.heap := by
  induction paths generalizing state memo with
  | nil => exact normal
  | cons paths rest ih =>
      apply bind _ _ (gate true g values paths state memo normal)
      intro primary middle current middleNormal
      cases primary
      · rw [ite_eq_right Bool.false_ne_true,select_state]
        exact ih middle current middleNormal
      · simp only [ite_true]
        apply bind _ _ (gate false s values paths middle current middleNormal)
        intro secondary later saved laterNormal
        cases secondary
        · simp only [Bool.false_eq_true,ite_false]
          apply bind _ _ (query p h n values paths later saved laterNormal)
          intro value checked fourth checkedNormal
          apply bind _ _ (decision p h budget paths value checked fourth checkedNormal)
          intro answer after final afterNormal
          cases answer
          · exact ih after final afterNormal
          · exact afterNormal
        · exact ih later saved laterNormal

private theorem map_state (first : SourceCurrentAllocatedScanWorker.Outcome SourceCurrentAllocatedRecordScanWorker.Result width) :
    (SourceCurrentAllocatedRecordScanWorker.mapPaths first).state = first.state := by
  cases first with
  | failed => rfl
  | done value => cases value; rfl

/-- Record Scan retains the same heap while it preserves original record occurrences. -/
theorem records [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (g s p h n budget : Nat) (values : List (Value Symbol Guard)) (records : List SourceEqualityClassOrder.Record)
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records state memo).state.native.machine.heap := by
  have retained := scan g s p h n budget values (records.map SourceEqualityClassOrder.Record.paths) state memo normal
  rw [←SourceCurrentAllocatedRecordScanWorker.scan_mapPaths,map_state] at retained
  exact retained
end MicroCFTA.SourceCurrentUnionNormalScan
