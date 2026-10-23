import MicroCFTA.SourceCurrentOriginalRowClusterScan
import MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth

namespace MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
variable {width : Nat}

/-- Read the complete state in every actual scan outcome. -/
def outcomeState (outcome : SourceCurrentOriginalRowClusterScan.Outcome width) :
    SourceCurrentSameSymbolEdgeControl.State width :=
  match outcome with
  | .yielded _ state | .done _ state | .failed _ state | .constraintError _ state | .blocked _ _ state => state

/-- One scan step retains or increases its actual constructor node counter. -/
theorem step_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : SourceCurrentOriginalRowClusterScan.Control)
    (state : SourceCurrentSameSymbolEdgeControl.State width) :
    state.checked.native.machine.heap.nodes.next ≤
      (outcomeState (SourceCurrentOriginalRowClusterScan.step control state)).checked.native.machine.heap.nodes.next := by
  cases control with
  | cluster candidates keptReversed =>
      cases candidates with
      | nil => exact Nat.le_refl _
      | cons pivot tail => exact Nat.le_refl _
  | scan pivot remaining incomparableReversed keptReversed =>
      cases remaining with
      | nil => exact Nat.le_refl _
      | cons candidate tail => exact Nat.le_refl _
  | comparison pivot candidate tail incomparableReversed keptReversed inner =>
      have pairGrowth : state.checked.native.machine.heap.nodes.next ≤
          (SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState
            (SourceCurrentSameSymbolEdgeControl.step inner state)).checked.native.machine.heap.nodes.next := by
        exact SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.step_mono inner state
      cases observed : SourceCurrentSameSymbolEdgeControl.step inner state with
      | yielded next after =>
          simpa only [SourceCurrentOriginalRowClusterScan.step, observed, outcomeState,
            SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState] using pairGrowth
      | done common after =>
          simpa only [SourceCurrentOriginalRowClusterScan.step, observed, outcomeState,
            SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState] using pairGrowth
      | failed reason after =>
          simpa only [SourceCurrentOriginalRowClusterScan.step, observed, outcomeState,
            SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState] using pairGrowth
      | constraintError message after =>
          simpa only [SourceCurrentOriginalRowClusterScan.step, observed, outcomeState,
            SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState] using pairGrowth
      | blocked reason next after =>
          simpa only [SourceCurrentOriginalRowClusterScan.step, observed, outcomeState,
            SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState] using pairGrowth

/-- Every finite scan outcome retains or increases its input node counter. -/
theorem execute_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : SourceCurrentOriginalRowClusterScan.Control)
    (state : SourceCurrentSameSymbolEdgeControl.State width) :
    state.checked.native.machine.heap.nodes.next ≤
      (outcomeState (SourceCurrentOriginalRowClusterScan.execute fuel control state)).checked.native.machine.heap.nodes.next := by
  induction fuel generalizing control state with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      have first : state.checked.native.machine.heap.nodes.next ≤
          (outcomeState (SourceCurrentOriginalRowClusterScan.step control state)).checked.native.machine.heap.nodes.next := by
        exact step_mono control state
      cases observed : SourceCurrentOriginalRowClusterScan.step control state with
      | yielded next after =>
          simp only [observed, outcomeState] at first
          simpa only [SourceCurrentOriginalRowClusterScan.execute, observed] using
            Nat.le_trans first (ih next after)
      | done values after =>
          simpa only [SourceCurrentOriginalRowClusterScan.execute, observed, outcomeState] using first
      | failed reason after =>
          simpa only [SourceCurrentOriginalRowClusterScan.execute, observed, outcomeState] using first
      | constraintError message after =>
          simpa only [SourceCurrentOriginalRowClusterScan.execute, observed, outcomeState] using first
      | blocked reason next after =>
          simpa only [SourceCurrentOriginalRowClusterScan.execute, observed, outcomeState] using first

end MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.outcomeState
#print MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.outcomeState
#print axioms MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.outcomeState
#check @MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.step_mono
#print MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.step_mono
#print axioms MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.step_mono
#check @MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.execute_mono
#print MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.execute_mono
#print axioms MicroCFTA.SourceCurrentOriginalRowClusterScanNodeCounterGrowth.execute_mono
