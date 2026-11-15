import MicroCFTA.SourceCurrentAllocatedNativeMuSource
import MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyReturned

/-!
# Returned properties through the actual Mu body

The selected source branch enters its literal child domain.
The child retains the actual optional-binder continuation.
Every child bound is below the original parent bound.
Optional construction preserves both memo tables for all of its outcomes.
No child-closure condition or future result law is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMuBodyReturned
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

set_option autoImplicit false

/-- Every optional-binder endpoint retains both returned laws, including pending construction. -/
theorem optional_binder_returned_all_fuels
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (key : Nat × Nat) (value : Value Symbol Guard) (state : Checked width)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (fuel : Nat) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.optionalBinder key value .pure)) state).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.optionalBinder key value .pure)) state).state.native.edges := by
  cases fuel with
  | zero => exact ⟨nodes, edges⟩
  | succ fuel =>
      cases built : SourceRecursiveIntersectionMaybeMu.maybeMu key value state.native.machine.heap with
      | pending pending heap =>
          simpa only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
            SourceRecursiveIntersectionNative.step, built, SourceEqualityNativeDemand.lift,
            Outcome.state, advance] using And.intro nodes edges
      | done result heap =>
          cases fuel <;>
            simpa only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
              SourceRecursiveIntersectionNative.step, built, SourceEqualityNativeDemand.lift,
              Outcome.state, advance] using And.intro nodes edges

/-- Every actual selected Mu-body endpoint retains both laws through its literal entered child. -/
theorem compile_node_mu_returned_all_fuels
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (state : Checked width) (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (fuel : Nat) (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (children :
      let entered := SourceRecursiveIntersectionEnvironment.enter state.native.machine.domains request.domain.key
        request.left request.right first second
      let started : Checked width :=
        {state with native := advance state.native {state.native.machine with domains := entered.2}}
      ∀ childFuel, childFuel < fuel →
        Steps 1 (.code (compileNode request)) state
          (.code ((requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
            (SourceRecursiveIntersectionKernel.body request.right)).bind (fun value =>
              .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure))) started →
        Returned nodeLaw started.native.nodes → Returned edgeLaw started.native.edges →
        Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
          (.code (requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
            (SourceRecursiveIntersectionKernel.body request.right))) started).state.native.nodes ∧
        Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
          (.code (requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
            (SourceRecursiveIntersectionKernel.body request.right))) started).state.native.edges) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel (.code (compileNode request)) state).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute fuel (.code (compileNode request)) state).state.native.edges := by
  let entered := SourceRecursiveIntersectionEnvironment.enter state.native.machine.domains request.domain.key
    request.left request.right first second
  let started : Checked width :=
    {state with native := advance state.native {state.native.machine with domains := entered.2}}
  let query := requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
    (SourceRecursiveIntersectionKernel.body request.right)
  let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun value => .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure
  have compiled : compileNode request = compileMu request.domain request.left request.right := by
    rcases selected with selected | selected | selected <;> simp only [compileNode, selected]
  have one : SourceEqualityNativeDemand.step (.code (compileNode request)) state =
      .yielded (.code (query.bind next)) started := by
    rw [compiled]
    exact SourceCurrentAllocatedNativeMuSource.enter_prefix request state first second leftIdentity rightIdentity
  have origin : Steps 1 (.code (compileNode request)) state (.code (query.bind next)) started :=
    .cons _ _ _ _ _ _ _ one (.refl _ _)
  have startedNodes : Returned nodeLaw started.native.nodes := nodes
  have startedEdges : Returned edgeLaw started.native.edges := edges
  change (∀ childFuel, childFuel < fuel →
    Steps 1 (.code (compileNode request)) state (.code (query.bind next)) started →
    Returned nodeLaw started.native.nodes → Returned edgeLaw started.native.edges →
    Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel (.code query) started).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel (.code query) started).state.native.edges) at children
  cases fuel with
  | zero => exact ⟨nodes, edges⟩
  | succ fuel =>
      rw [SourceEqualityNativeDemand.execute, one]
      rcases SourceCurrentAllocatedNativeEdgeBodyReturned.bind_endpoint_state_cases
        fuel (.code query) next started with same | ⟨steps, value, middle, shorter, called, same⟩
      · simp only [Control.bind] at same
        rw [same]
        exact children fuel (by omega) origin startedNodes startedEdges
      · simp only [Control.bind] at same
        have completed := trace_done steps _ started middle value called
        have atMiddle := children (steps + 1) (by omega) origin startedNodes startedEdges
        rw [completed] at atMiddle
        rw [same]
        exact optional_binder_returned_all_fuels nodeLaw edgeLaw
          (SourceRecursiveIntersectionControl.pair first second) value middle
          atMiddle.1 atMiddle.2 (fuel - steps)

end MicroCFTA.SourceCurrentAllocatedNativeMuBodyReturned
