import MicroCFTA.SourceCurrentAllocatedNativePrefixInputs
import MicroCFTA.SourceCurrentAllocatedNativeBodyCodeReturned
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryReturned
import MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryReturned
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryResult
import MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryResult
import MicroCFTA.SourceCurrentAllocatedNativeRawBodyResults

/-!
# Fixed native query laws at every supplied budget

Closed self queries retain the original value.
Rows with unequal arities retain the actual empty sentinel.
The same induction preserves both returned laws at every endpoint.
Raw result traces do not spend a further pure-return observation step.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat}

set_option autoImplicit false

/-- Closed equal operands return the complete original value. -/
def SelfResult (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  request.right = request.left → request.left.free = [] → value = request.left

/-- Unequal row arities return the actual empty sentinel. -/
def MismatchResult (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) : Prop :=
  request.left.children.length ≠ request.right.children.length → row.children = [.empty]

private theorem through_current {Output : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : Checked width)
    (plan : InputsThrough fuel control state) : Inputs control state := by
  cases fuel with
  | zero => exact plan
  | succ => exact plan.1

private theorem through_mono {Output : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (large small : Nat) (control : Control Output) (state : Checked width)
    (bounded : small ≤ large) (plan : InputsThrough large control state) :
    InputsThrough small control state := by
  induction large generalizing small control state with
  | zero =>
      have same : small = 0 := by omega
      subst small
      exact plan
  | succ large ih =>
      cases small with
      | zero => exact plan.1
      | succ small =>
          refine ⟨plan.1, ?_⟩
          cases one : step control state with
          | yielded next after =>
              have remaining := plan.2
              rw [one] at remaining
              exact ih small next after (by omega) remaining
          | done | failed | constraintError | blocked => trivial

set_option maxHeartbeats 1600000 in
/-- Both memo laws hold at every query endpoint and every bounded raw pure return. -/
theorem query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
      Physical before.native →
      InputsThrough fuel (.code (.node request .pure)) before →
      Returned SelfResult before.native.nodes → Returned MismatchResult before.native.edges →
      (Returned SelfResult (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
        Returned MismatchResult (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
        SelfResult request value)) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
      Physical before.native →
      InputsThrough fuel (.code (.edge request .pure)) before →
      Returned SelfResult before.native.nodes → Returned MismatchResult before.native.edges →
      (Returned SelfResult (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
        Returned MismatchResult (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
        MismatchResult request value)) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have nodeChild {Output : Type}
          (original : Control Output) (initial : Checked width)
          (physical : Physical initial.native) (plan : InputsThrough fuel original initial)
          (request : NodeRequest Symbol Guard)
          (next : Value Symbol Guard → Code Symbol Guard Output) (before : Checked width)
          (used childFuel : Nat) (bounded : used + childFuel ≤ fuel) (smaller : childFuel < fuel)
          (origin : Steps used original initial
            (.code ((requestNode request.domain request.left request.right).bind next)) before)
          (nodes : Returned SelfResult before.native.nodes)
          (edges : Returned MismatchResult before.native.edges) := by
        have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
          fuel used original (.code (requestNode request.domain request.left request.right))
          next initial before physical plan origin (by omega)
        have childPlan := through_mono (fuel - used) childFuel _ before (by omega) reached.2.2.2.2
        exact (ih childFuel smaller).1 request before reached.2.1 childPlan nodes edges
      have edgeChild {Output : Type}
          (original : Control Output) (initial : Checked width)
          (physical : Physical initial.native) (plan : InputsThrough fuel original initial)
          (request : EdgeRequest Symbol Guard)
          (next : EdgeValue Symbol Guard → Code Symbol Guard Output) (before : Checked width)
          (used childFuel : Nat) (bounded : used + childFuel ≤ fuel) (smaller : childFuel < fuel)
          (origin : Steps used original initial
            (.code ((requestEdge request.domain request.left request.right).bind next)) before)
          (nodes : Returned SelfResult before.native.nodes)
          (edges : Returned MismatchResult before.native.edges) := by
        have reached := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
          fuel used original (.code (requestEdge request.domain request.left request.right))
          next initial before physical plan origin (by omega)
        have childPlan := through_mono (fuel - used) childFuel _ before (by omega) reached.2.2.2.2
        exact (ih childFuel smaller).2 request before reached.2.1 childPlan nodes edges
      constructor
      · intro request before physical plan nodes edges
        have current := through_current fuel (.code (.node request .pure)) before plan
        have bodyBundle : ∀ bodyFuel, bodyFuel < fuel →
            ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (first : Checked width),
            Steps 1 (.code (.node request .pure)) before
              (.code ((compileNode request).bind next)) first →
            Returned SelfResult first.native.nodes → Returned MismatchResult first.native.edges →
            Returned SelfResult (execute bodyFuel (.code (compileNode request)) first).state.native.nodes ∧
            Returned MismatchResult (execute bodyFuel (.code (compileNode request)) first).state.native.edges ∧
            (∀ (value : Value Symbol Guard) (middle : Checked width),
              Steps bodyFuel (.code (compileNode request)) first (.code (.pure value)) middle →
              SelfResult request value) := by
          intro bodyFuel smaller next first entered firstNodes firstEdges
          have preserved :=
            SourceCurrentAllocatedNativeBodyCodeReturned.body_code_returned_of_outer_query_induction
              SelfResult MismatchResult (.code (.node request .pure)) before fuel
              (fun child childNext childBefore used childFuel _positive bounded small origin childNodes childEdges =>
                (nodeChild (.code (.node request .pure)) before physical plan child childNext childBefore
                  used childFuel bounded small origin childNodes childEdges).1)
              (fun child childNext childBefore used childFuel _positive bounded small origin childNodes childEdges =>
                (edgeChild (.code (.node request .pure)) before physical plan child childNext childBefore
                  used childFuel bounded small origin childNodes childEdges).1)
              (compileNode request) (compileNode_bodyCode request)
              next first 1 bodyFuel (by decide) (by omega) entered firstNodes firstEdges
          refine ⟨preserved.1, preserved.2, ?_⟩
          intro value middle actual
          apply SourceCurrentAllocatedNativeRawBodyResults.compile_node_closed_self_trace_result
            request before first middle fuel bodyFuel value next entered smaller actual
          intro childSteps small childNext childValue childAfter childEntry childTrace closed
          have child := nodeChild (.code (.node request .pure)) before physical plan
            ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.left⟩ childNext first
            1 childSteps (by omega) small childEntry firstNodes firstEdges
          exact child.2 childSteps childValue childAfter (by omega) childTrace rfl closed
        have preserved := SourceCurrentAllocatedNativeNodeQueryReturned.node_query_returned_of_body_induction
          SelfResult MismatchResult request before fuel physical current.1 current.2 nodes edges bodyBundle
        refine ⟨preserved, ?_⟩
        intro count value after bounded actual
        apply SourceCurrentAllocatedNativeNodeQueryResult.node_query_result_of_body_induction
          SelfResult request before after (count + 1) value physical current.1 current.2 nodes
          (trace_done count _ before after value actual)
        intro bodySteps shorter next first middle result entered bodyTrace
        have oneEndpoint := SourceCurrentAllocatedNativeNodeQueryReturned.node_query_returned_of_body_induction
          SelfResult MismatchResult request before 1 physical current.1 current.2 nodes edges
          (fun bodyFuel small childNext childFirst origin childNodes childEdges =>
            bodyBundle bodyFuel (by omega) childNext childFirst origin childNodes childEdges)
        have firstLaws : Returned SelfResult first.native.nodes ∧ Returned MismatchResult first.native.edges := by
          have firstRun := entered.execute
          simp only [requestNode] at firstRun
          simpa only [firstRun, Outcome.state] using oneEndpoint
        exact (bodyBundle bodySteps (by omega) next first entered firstLaws.1 firstLaws.2).2.2
          result middle bodyTrace
      · intro request before physical plan nodes edges
        have current := through_current fuel (.code (.edge request .pure)) before plan
        have bodyBundle : ∀ bodyFuel, bodyFuel < fuel →
            ∀ (next : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) (first : Checked width),
            Steps 1 (.code (.edge request .pure)) before (.edgeBody request next) first →
            Returned SelfResult first.native.nodes → Returned MismatchResult first.native.edges →
            Returned SelfResult (execute bodyFuel (.edgeBody request .pure) first).state.native.nodes ∧
            Returned MismatchResult (execute bodyFuel (.edgeBody request .pure) first).state.native.edges ∧
            (∀ (value : EdgeValue Symbol Guard) (middle : Checked width),
              Steps bodyFuel (.edgeBody request .pure) first (.code (.pure value)) middle →
              MismatchResult request value) := by
          intro bodyFuel smaller next first entered firstNodes firstEdges
          have firstResources := SourceCurrentAllocatedNativePrefixInputs.prefix_inputs_before_bind
            fuel 1 (.code (.edge request .pure)) (.edgeBody request .pure) next before first
            physical plan entered (by omega)
          have preserved := SourceCurrentAllocatedNativeEdgeBodyReturned.edge_body_returned_all_fuels
            SelfResult MismatchResult request first bodyFuel firstNodes firstEdges (by
              intro used childFuel _positive bounded small pair _member childNext childBefore origin childNodes childEdges
              let joinedNext : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) :=
                fun value => (childNext value).bind next
              have lifted : Steps used (.edgeBody request next) first
                  (.code ((requestNode request.domain pair.1 pair.2).bind joinedNext)) childBefore := by
                simpa only [Control.bind, Code.bind, Code.bind_assoc, joinedNext] using origin.bind _ _ _ _ _ next
              have joined := entered.trans 1 used _ _ _ _ _ _ lifted
              exact (nodeChild (.code (.edge request .pure)) before physical plan
                ⟨request.domain, pair.1, pair.2⟩ joinedNext childBefore (1 + used) childFuel
                (by omega) (Nat.lt_trans small smaller) joined childNodes childEdges).1)
          refine ⟨preserved.1, preserved.2, ?_⟩
          intro value middle actual mismatch
          exact (SourceCurrentAllocatedNativeRawBodyResults.mismatch_edge_body_trace_result
            request first middle bodyFuel value firstResources.2.1 mismatch actual).1
        have preserved := SourceCurrentAllocatedNativeEdgeQueryReturned.edge_query_returned_of_body_induction
          SelfResult MismatchResult request before fuel physical current.1 current.2 nodes edges bodyBundle
        refine ⟨preserved, ?_⟩
        intro count value after bounded actual
        apply SourceCurrentAllocatedNativeEdgeQueryResult.edge_query_result_of_body_induction
          MismatchResult request before after (count + 1) value physical current.1 current.2 edges
          (trace_done count _ before after value actual)
        intro bodySteps shorter next first middle result entered bodyTrace
        have oneEndpoint := SourceCurrentAllocatedNativeEdgeQueryReturned.edge_query_returned_of_body_induction
          SelfResult MismatchResult request before 1 physical current.1 current.2 nodes edges
          (fun bodyFuel small childNext childFirst origin childNodes childEdges =>
            bodyBundle bodyFuel (by omega) childNext childFirst origin childNodes childEdges)
        have firstLaws : Returned SelfResult first.native.nodes ∧ Returned MismatchResult first.native.edges := by
          have firstRun := entered.execute
          simp only [requestEdge] at firstRun
          simpa only [firstRun, Outcome.state] using oneEndpoint
        exact (bodyBundle bodySteps (by omega) next first entered firstLaws.1 firstLaws.2).2.2
          result middle bodyTrace

/-- The actual initial node query starts with both complete memo families empty. -/
theorem initial_node_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel : Nat) (request : NodeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.node request .pure)) ⟨initial width machine, operations⟩) :
    (Returned SelfResult (execute fuel (.code (.node request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned MismatchResult (execute fuel (.code (.node request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.node request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      SelfResult request value) := by
  exact (query_returned_and_raw_results fuel).1 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid) plan
    (SourceCurrentAllocatedNativeContextCache.returned_empty SelfResult)
    (SourceCurrentAllocatedNativeContextCache.returned_empty MismatchResult)

/-- The actual initial edge query starts with both complete memo families empty. -/
theorem initial_edge_query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel : Nat) (request : EdgeRequest Symbol Guard)
    (plan : InputsThrough fuel (.code (.edge request .pure)) ⟨initial width machine, operations⟩) :
    (Returned SelfResult (execute fuel (.code (.edge request .pure))
      ⟨initial width machine, operations⟩).state.native.nodes ∧
      Returned MismatchResult (execute fuel (.code (.edge request .pure))
        ⟨initial width machine, operations⟩).state.native.edges) ∧
    (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
      Steps count (.code (.edge request .pure)) ⟨initial width machine, operations⟩ (.code (.pure value)) after →
      MismatchResult request value) := by
  exact (query_returned_and_raw_results fuel).2 request ⟨initial width machine, operations⟩
    (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid) plan
    (SourceCurrentAllocatedNativeContextCache.returned_empty SelfResult)
    (SourceCurrentAllocatedNativeContextCache.returned_empty MismatchResult)

end MicroCFTA.SourceCurrentAllocatedNativeQueryGlobalLaws
