import MicroCFTA.SourceCurrentAllocatedNativeAdmissionCache
import MicroCFTA.SourceEqualityNativeDemandOperations

/-!
# Causal request admission through actual checked execution

Only a node or edge lookup can publish a new request.
Its current operands and seen pairs must belong to the fixed inventory.
Every other instruction retains the requests in all memo phases.
The execution theorem uses checks on the actual reached instructions.
Source certificates must still derive those checks for a complete query.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution
open Language IntersectSchedule InternedConstructorTemplates
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand SourceCurrentAllocatedNativeAdmissionCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} {view : View Symbol}

/-- Only an instruction that can publish a request needs current admission. -/
def RequestCovered (inputs : FiniteInput view) : Control Output → Prop
  | .code (.node request _) => NodeCovered inputs request
  | .code (.edge request _) => EdgeCovered inputs request
  | _ => True

/-- Checked edge-body allocation leaves all native requests unchanged. -/
theorem body_covered (inputs : FiniteInput view)
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (state : Checked width) (covered : Covered inputs state.native) :
    Covered inputs (body request next state).state.native := by
  rw [SourceEqualityNativeDemandOperations.body_native]
  exact covered

/-- Actual publication checks derive coverage in every returned memo phase. -/
theorem step_covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inputs : FiniteInput view) (control : Control Output) (state : Checked width)
    (covered : Covered inputs state.native) (current : RequestCovered inputs control) :
    Covered inputs (step control state).state.native := by
  cases control with
  | edgeBody request next => exact body_covered inputs request next state covered
  | code code =>
      cases code with
      | pure | fail | read => exact covered
      | work job next => exact advance_covered inputs state.native _ covered
      | enter domain left right first second next => exact advance_covered inputs state.native _ covered
      | optionalBinder pair value next =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair value state.native.machine.heap with
          | done result heap | pending key heap =>
              simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state] using
                advance_covered inputs state.native {state.native.machine with heap := heap} covered
      | node request next =>
          have chosenCovered := lookupNode_covered inputs state.native request covered current
          cases lookup : lookupNode width request state.native with
          | mk selection chosen =>
              simp only [lookup] at chosenCovered
              cases selection with
              | direct actual =>
                  simpa only [step, SourceRecursiveIntersectionNative.step, lookup, lift, Outcome.state] using chosenCovered
              | memoized handle =>
                  have currentCovered := demandNode_covered inputs chosen handle chosenCovered
                  cases demand : demandNode handle chosen with
                  | mk observation after =>
                      simp only [demand] at currentCovered
                      cases observation <;>
                        simpa only [step, SourceRecursiveIntersectionNative.step, lookup, demand, lift, Outcome.state] using currentCovered
      | edge request next =>
          have chosenCovered := lookupEdge_covered inputs state.native request covered current
          cases lookup : lookupEdge width request state.native with
          | mk handle chosen =>
              simp only [lookup] at chosenCovered
              have currentCovered := demandEdge_covered inputs chosen handle chosenCovered
              cases demand : demandEdge handle chosen with
              | mk observation after =>
                  simp only [demand] at currentCovered
                  cases observation <;>
                    simpa only [step, lookup, demand, Outcome.state] using currentCovered
      | finishNode handle value next => exact finishNode_covered inputs state.native handle value covered
      | finishEdge handle value next => exact finishEdge_covered inputs state.native handle value covered

/-- Admission checks follow only the finite interpreter's actual reached controls. -/
noncomputable def RequestsThrough [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inputs : FiniteInput view) : Nat → Control Output → Checked width → Prop
  | 0, _, _ => True
  | fuel + 1, control, state =>
      RequestCovered inputs control ∧ match step control state with
      | .yielded next after => RequestsThrough inputs fuel next after
      | .done _ _ | .failed _ _ | .constraintError _ _ | .blocked _ _ _ => True

/-- All actual finite outcomes retain admitted original requests in both native tables. -/
theorem execute_covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inputs : FiniteInput view) (fuel : Nat) (control : Control Output) (state : Checked width)
    (covered : Covered inputs state.native) (requests : RequestsThrough inputs fuel control state) :
    Covered inputs (execute fuel control state).state.native := by
  induction fuel generalizing control state with
  | zero => exact covered
  | succ fuel ih =>
      have one := step_covered inputs control state covered requests.1
      cases actual : step control state with
      | yielded next after =>
          have afterCovered : Covered inputs after.native := by simpa only [actual, Outcome.state] using one
          have tail : RequestsThrough inputs fuel next after := by
            simpa only [RequestsThrough, actual] using requests.2
          simpa only [SourceEqualityNativeDemand.execute, actual] using ih next after afterCovered tail
      | done | failed | constraintError | blocked =>
          simpa only [SourceEqualityNativeDemand.execute, actual, Outcome.state] using one

/-- A completed query supplies actual returned-cell admission and captured-pair coverage. -/
theorem done_admitted [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (inputs : FiniteInput view) (fuel : Nat) (control : Control Output)
    (before after : Checked width) (value : Output)
    (covered : Covered inputs before.native) (requests : RequestsThrough inputs fuel control before)
    (done : execute fuel control before = .done value after) :
    Covered inputs after.native ∧
      SourceCurrentAllocatedNativeInputModelTransport.Admitted view (finiteInputMeaning view inputs) after.native ∧
      SourceCurrentAllocatedNativeContextRebase.SeenAdmitted inputs after.native := by
  have actual : Covered inputs after.native := by
    simpa only [done, Outcome.state] using execute_covered inputs fuel control before covered requests
  exact ⟨actual, actual.admitted, actual.seen_admitted⟩
end MicroCFTA.SourceCurrentAllocatedNativeAdmissionExecution
