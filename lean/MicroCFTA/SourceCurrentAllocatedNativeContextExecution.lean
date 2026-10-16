import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceEqualityNativeDemandOperations

/-!
# Contextual cache retention through actual checked execution

Only an executed finish instruction needs a new local semantic law. Its law
refers to the original request in the current evaluating cell. Lookup,
demand, physical effects, and checked edge bodies retain existing laws.
Every finite outcome uses the actual checked state and operation cache.
This module does not derive recursive finish laws or native completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeContextExecution
open Language InternedConstructorTemplates
open SourceRecursiveIntersectionKernel (Machine)
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State

variable (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
  (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)

/-- Only a currently evaluating cell receives a new contextual result obligation. -/
def FinishLaw : Control Output → Checked width → Prop
  | .code (.finishNode handle value _), state => ∀ request,
      state.native.nodes.cells handle = some ⟨request, .evaluating⟩ → NodeLaw view model ranked holds request value
  | .code (.finishEdge handle value _), state => ∀ request,
      state.native.edges.cells handle = some ⟨request, .evaluating⟩ → EdgeLaw view model ranked holds request value
  | _, _ => True

private theorem finish_node (state : Native width Symbol Guard) (handle : Nat) (value : Value Symbol Guard)
    (valid : Contextual view model ranked holds state)
    (localLaw : ∀ request, state.nodes.cells handle = some ⟨request, .evaluating⟩ →
      NodeLaw view model ranked holds request value) :
    Contextual view model ranked holds (SourceRecursiveIntersectionThunks.finishNode handle value state) := by
  cases found : state.nodes.cells handle with
  | none => simpa only [SourceRecursiveIntersectionThunks.finishNode, FlatMemoThunk.finish, found] using valid
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | suspended | returned result =>
              simpa only [SourceRecursiveIntersectionThunks.finishNode, FlatMemoThunk.finish, found] using valid
          | evaluating =>
              exact finishNode_contextual view model ranked holds state handle request value valid found (localLaw request found)

private theorem finish_edge (state : Native width Symbol Guard) (handle : Nat) (value : EdgeValue Symbol Guard)
    (valid : Contextual view model ranked holds state)
    (localLaw : ∀ request, state.edges.cells handle = some ⟨request, .evaluating⟩ →
      EdgeLaw view model ranked holds request value) :
    Contextual view model ranked holds (SourceRecursiveIntersectionThunks.finishEdge handle value state) := by
  cases found : state.edges.cells handle with
  | none => simpa only [SourceRecursiveIntersectionThunks.finishEdge, FlatMemoThunk.finish, found] using valid
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | suspended | returned result =>
              simpa only [SourceRecursiveIntersectionThunks.finishEdge, FlatMemoThunk.finish, found] using valid
          | evaluating =>
              exact finishEdge_contextual view model ranked holds state handle request value valid found (localLaw request found)

/-- Every checked edge-body outcome retains the same native contextual cache. -/
theorem body_contextual (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : Checked width) (valid : Contextual view model ranked holds state.native) :
    Contextual view model ranked holds (body request next state).state.native := by
  rw [SourceEqualityNativeDemandOperations.body_native]
  exact valid

/-- One actual checked step retains contextual laws from its local finish obligation alone. -/
theorem step_contextual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : Checked width) (valid : Contextual view model ranked holds state.native)
    (localLaw : FinishLaw view model ranked holds control state) :
    Contextual view model ranked holds (step control state).state.native := by
  cases control with
  | edgeBody request next => exact body_contextual view model ranked holds request next state valid
  | code code =>
      cases code with
      | pure | fail | read => exact valid
      | work job next => exact advance_contextual view model ranked holds state.native _ valid
      | enter domain left right first second next => exact advance_contextual view model ranked holds state.native _ valid
      | optionalBinder pair value next =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair value state.native.machine.heap with
          | done result heap | pending key heap =>
              simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state] using
                advance_contextual view model ranked holds state.native {state.native.machine with heap := heap} valid
      | node request next =>
          have chosenValid := lookupNode_contextual view model ranked holds state.native request valid
          cases lookup : lookupNode width request state.native with
          | mk selection chosen =>
              simp only [lookup] at chosenValid
              cases selection with
              | direct actual => simpa only [step, SourceRecursiveIntersectionNative.step, lookup, lift, Outcome.state] using chosenValid
              | memoized handle =>
                  have currentValid := demandNode_contextual view model ranked holds chosen handle chosenValid
                  cases demand : demandNode handle chosen with
                  | mk observation current =>
                      simp only [demand] at currentValid
                      cases observation <;>
                        simpa only [step, SourceRecursiveIntersectionNative.step, lookup, demand, lift, Outcome.state] using currentValid
      | edge request next =>
          have chosenValid := lookupEdge_contextual view model ranked holds state.native request valid
          cases lookup : lookupEdge width request state.native with
          | mk handle chosen =>
              simp only [lookup] at chosenValid
              have currentValid := demandEdge_contextual view model ranked holds chosen handle chosenValid
              cases demand : demandEdge handle chosen with
              | mk observation current =>
                  simp only [demand] at currentValid
                  cases observation <;> simpa only [step, lookup, demand, Outcome.state] using currentValid
      | finishNode handle value next =>
          exact finish_node view model ranked holds state.native handle value valid localLaw
      | finishEdge handle value next =>
          exact finish_edge view model ranked holds state.native handle value valid localLaw

/-- Local finish laws are required only for instructions that the finite execution performs. -/
noncomputable def FinishThrough [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Control Output → Checked width → Prop
  | 0, _, _ => True
  | fuel + 1, control, state =>
      FinishLaw view model ranked holds control state ∧ match step control state with
      | .yielded next after => FinishThrough fuel next after
      | .done _ _ | .failed _ _ | .constraintError _ _ | .blocked _ _ _ => True

/-- All actual finite outcomes retain contextual completed cells at their exact returned state. -/
theorem execute_contextual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : Checked width)
    (valid : Contextual view model ranked holds state.native)
    (localLaws : FinishThrough view model ranked holds fuel control state) :
    Contextual view model ranked holds (execute fuel control state).state.native := by
  induction fuel generalizing control state with
  | zero => exact valid
  | succ fuel ih =>
      have one := step_contextual view model ranked holds control state valid localLaws.1
      cases actual : step control state with
      | yielded next after =>
          have current : Contextual view model ranked holds after.native := by
            simpa only [actual, Outcome.state] using one
          have rest : FinishThrough view model ranked holds fuel next after := by
            simpa only [FinishThrough, actual] using localLaws.2
          simpa only [execute, actual] using ih next after current rest
      | done | failed | constraintError | blocked =>
          simpa only [execute, actual, Outcome.state] using one

/-- A completed checked trace retains the same contextual invariant without a final-validity premise. -/
theorem done_contextual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (before after : Checked width) (value : Output)
    (valid : Contextual view model ranked holds before.native)
    (localLaws : FinishThrough view model ranked holds fuel control before)
    (done : execute fuel control before = .done value after) :
    Contextual view model ranked holds after.native := by
  simpa only [done, Outcome.state] using execute_contextual view model ranked holds fuel control before valid localLaws

end MicroCFTA.SourceCurrentAllocatedNativeContextExecution
