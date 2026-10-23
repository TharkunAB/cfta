import MicroCFTA.SourceCurrentSameSymbolEdgeControl
import MicroCFTA.SourceEqualityNativeDemandNodeCounterGrowth

namespace MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
variable {width : Nat}

/-- Read the complete state in every actual comparison outcome. -/
def outcomeState (outcome : SourceCurrentSameSymbolEdgeControl.Outcome width) :
    SourceCurrentSameSymbolEdgeControl.State width :=
  match outcome with
  | .yielded _ state | .done _ state | .failed _ state | .constraintError _ state | .blocked _ _ state => state

/-- One comparison step retains or increases its actual constructor node counter. -/
theorem step_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : SourceCurrentSameSymbolEdgeControl.Control)
    (state : SourceCurrentSameSymbolEdgeControl.State width) :
    state.checked.native.machine.heap.nodes.next ≤
      (outcomeState (SourceCurrentSameSymbolEdgeControl.step control state)).checked.native.machine.heap.nodes.next := by
  cases control with
  | call request pending => exact Nat.le_refl _
  | demand handle pending =>
      cases observed : (FlatMemoThunk.demand handle state.memo).1 with
      | absent =>
          simp only [SourceCurrentSameSymbolEdgeControl.step, observed, outcomeState]
          exact Nat.le_refl _
      | evaluate request =>
          simp only [SourceCurrentSameSymbolEdgeControl.step, observed, outcomeState]
          exact Nat.le_refl _
      | busy =>
          simp only [SourceCurrentSameSymbolEdgeControl.step, observed, outcomeState]
          exact Nat.le_refl _
      | ready value =>
          simp only [SourceCurrentSameSymbolEdgeControl.step, observed, outcomeState]
          exact Nat.le_refl _
  | order handle request pending =>
      by_cases reversed : request.2.entry.identity < request.1.entry.identity
      · simp only [SourceCurrentSameSymbolEdgeControl.step, reversed, ↓reduceIte, outcomeState]
        exact Nat.le_refl _
      · simp only [SourceCurrentSameSymbolEdgeControl.step, reversed, ↓reduceIte, outcomeState]
        exact Nat.le_refl _
  | native body pending =>
      have nativeGrowth : state.checked.native.machine.heap.nodes.next ≤
          (SourceEqualityNativeDemand.step body state.checked).state.native.machine.heap.nodes.next := by
        exact SourceEqualityNativeDemandNodeCounterGrowth.step_mono body state.checked
      cases observed : SourceEqualityNativeDemand.step body state.checked with
      | yielded next after =>
          simpa only [SourceCurrentSameSymbolEdgeControl.step, observed, outcomeState,
            SourceEqualityNativeDemand.Outcome.state] using nativeGrowth
      | done value after =>
          simpa only [SourceCurrentSameSymbolEdgeControl.step, observed, outcomeState,
            SourceEqualityNativeDemand.Outcome.state] using nativeGrowth
      | failed failure after =>
          simpa only [SourceCurrentSameSymbolEdgeControl.step, observed, outcomeState,
            SourceEqualityNativeDemand.Outcome.state] using nativeGrowth
      | constraintError message after =>
          simpa only [SourceCurrentSameSymbolEdgeControl.step, observed, outcomeState,
            SourceEqualityNativeDemand.Outcome.state] using nativeGrowth
      | blocked reason next after =>
          simpa only [SourceCurrentSameSymbolEdgeControl.step, observed, outcomeState,
            SourceEqualityNativeDemand.Outcome.state] using nativeGrowth
  | ret value pending =>
      cases pending with
      | nil => exact Nat.le_refl _
      | cons handle pending => exact Nat.le_refl _

/-- Every finite comparison outcome retains or increases its input node counter. -/
theorem execute_mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : SourceCurrentSameSymbolEdgeControl.Control)
    (state : SourceCurrentSameSymbolEdgeControl.State width) :
    state.checked.native.machine.heap.nodes.next ≤
      (outcomeState (SourceCurrentSameSymbolEdgeControl.execute fuel control state)).checked.native.machine.heap.nodes.next := by
  induction fuel generalizing control state with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      have first : state.checked.native.machine.heap.nodes.next ≤
          (outcomeState (SourceCurrentSameSymbolEdgeControl.step control state)).checked.native.machine.heap.nodes.next := by
        exact step_mono control state
      cases observed : SourceCurrentSameSymbolEdgeControl.step control state with
      | yielded next after =>
          simp only [observed, outcomeState] at first
          simpa only [SourceCurrentSameSymbolEdgeControl.execute, observed] using
            Nat.le_trans first (ih next after)
      | done value after =>
          simpa only [SourceCurrentSameSymbolEdgeControl.execute, observed, outcomeState] using first
      | failed failure after =>
          simpa only [SourceCurrentSameSymbolEdgeControl.execute, observed, outcomeState] using first
      | constraintError message after =>
          simpa only [SourceCurrentSameSymbolEdgeControl.execute, observed, outcomeState] using first
      | blocked reason next after =>
          simpa only [SourceCurrentSameSymbolEdgeControl.execute, observed, outcomeState] using first

end MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth

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
#check @MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState
#print MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState
#print axioms MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState
#check @MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.step_mono
#print MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.step_mono
#print axioms MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.step_mono
#check @MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.execute_mono
#print MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.execute_mono
#print axioms MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.execute_mono
