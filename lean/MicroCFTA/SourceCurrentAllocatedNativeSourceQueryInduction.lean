import MicroCFTA.SourceCurrentAllocatedNativePrefixOperations
import MicroCFTA.SourceCurrentAllocatedNativeBodyCodeReturned
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryReturned
import MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryReturned
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryResult
import MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryResult

/-!
# Native query induction with concrete source and operations

The fixed source heap grows to each actual query state.
The original field plan preserves valid operation caches at each prefix.
Both existing Returned predicates hold at every supplied endpoint.
Result rules receive derived resources at the actual first state.
Child rules retain the same outer query and original fuel.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeSourceQueryInduction
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough Inputs)
open SourceEqualityNativeDemandOperations (FieldsThrough)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat}

set_option autoImplicit false

private theorem through_current {Output : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : Checked width)
    (plan : InputsThrough fuel control state) : Inputs control state := by
  cases fuel with
  | zero => exact plan
  | succ => exact plan.1

theorem through_mono {Output : Type}
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

theorem fields_mono {Output : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (large small : Nat) (control : Control Output) (state : Checked width)
    (bounded : small ≤ large) (plan : FieldsThrough large control state) :
    FieldsThrough small control state := by
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
/-- Actual source prefixes derive concrete resources and both memo laws for each smaller query. -/
theorem query_returned_and_raw_results
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (nodeResults : ∀ (request : NodeRequest Symbol Guard)
      (before first middle : Checked width) (parentFuel bodySteps : Nat)
      (value : Value Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough parentFuel (.code (.node request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough parentFuel (.code (.node request .pure)) before →
      Steps 1 (.code (.node request .pure)) before (.code ((compileNode request).bind next)) first →
      Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      bodySteps < parentFuel →
      Steps bodySteps (.code (compileNode request)) first (.code (.pure value)) middle →
      (∀ (child : NodeRequest Symbol Guard)
        (childNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (childBefore childAfter : Checked width) (used count : Nat) (childValue : Value Symbol Guard),
        0 < used → used + count ≤ parentFuel →
        Steps used (.code (.node request .pure)) before
          (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore →
        Steps count (.code (requestNode child.domain child.left child.right)) childBefore
          (.code (.pure childValue)) childAfter → nodeLaw child childValue) →
      (∀ (child : EdgeRequest Symbol Guard)
        (childNext : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (childBefore childAfter : Checked width) (used count : Nat) (childValue : EdgeValue Symbol Guard),
        0 < used → used + count ≤ parentFuel →
        Steps used (.code (.node request .pure)) before
          (.code ((requestEdge child.domain child.left child.right).bind childNext)) childBefore →
        Steps count (.code (requestEdge child.domain child.left child.right)) childBefore
          (.code (.pure childValue)) childAfter → edgeLaw child childValue) →
      nodeLaw request value)
    (edgeResults : ∀ (request : EdgeRequest Symbol Guard)
      (before first middle : Checked width) (parentFuel bodySteps : Nat)
      (value : EdgeValue Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough parentFuel (.code (.edge request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough parentFuel (.code (.edge request .pure)) before →
      Steps 1 (.code (.edge request .pure)) before (.edgeBody request next) first →
      Grows sourceHeap first.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid first.operations →
      bodySteps < parentFuel →
      Steps bodySteps (.edgeBody request .pure) first (.code (.pure value)) middle →
      (∀ (child : NodeRequest Symbol Guard)
        (childNext : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (childBefore childAfter : Checked width) (used count : Nat) (childValue : Value Symbol Guard),
        0 < used → used + count ≤ parentFuel →
        Steps used (.code (.edge request .pure)) before
          (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore →
        Steps count (.code (requestNode child.domain child.left child.right)) childBefore
          (.code (.pure childValue)) childAfter → nodeLaw child childValue) →
      (∀ (child : EdgeRequest Symbol Guard)
        (childNext : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (childBefore childAfter : Checked width) (used count : Nat) (childValue : EdgeValue Symbol Guard),
        0 < used → used + count ≤ parentFuel →
        Steps used (.code (.edge request .pure)) before
          (.code ((requestEdge child.domain child.left child.right).bind childNext)) childBefore →
        Steps count (.code (requestEdge child.domain child.left child.right)) childBefore
          (.code (.pure childValue)) childAfter → edgeLaw child childValue) →
      edgeLaw request value)
    (fuel : Nat) :
    (∀ (request : NodeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.node request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.node request .pure)) before →
      Returned nodeLaw before.native.nodes → Returned edgeLaw before.native.edges →
      (Returned nodeLaw (execute fuel (.code (.node request .pure)) before).state.native.nodes ∧
        Returned edgeLaw (execute fuel (.code (.node request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : Value Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.node request .pure)) before (.code (.pure value)) after →
        nodeLaw request value)) ∧
    (∀ (request : EdgeRequest Symbol Guard) (before : Checked width),
      Physical before.native → Grows sourceHeap before.native.machine.heap →
      SourceEqualityConstraintMemoAllocation.Valid before.operations →
      InputsThrough fuel (.code (.edge request .pure)) before →
      SourceEqualityNativeDemandOperations.FieldsThrough fuel (.code (.edge request .pure)) before →
      Returned nodeLaw before.native.nodes → Returned edgeLaw before.native.edges →
      (Returned nodeLaw (execute fuel (.code (.edge request .pure)) before).state.native.nodes ∧
        Returned edgeLaw (execute fuel (.code (.edge request .pure)) before).state.native.edges) ∧
      (∀ (count : Nat) (value : EdgeValue Symbol Guard) (after : Checked width), count ≤ fuel →
        Steps count (.code (.edge request .pure)) before (.code (.pure value)) after →
        edgeLaw request value)) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have nodeChild {Output : Type}
          (original : Control Output) (initial : Checked width)
          (physical : Physical initial.native)
          (sourceGrowth : Grows sourceHeap initial.native.machine.heap)
          (valid : SourceEqualityConstraintMemoAllocation.Valid initial.operations)
          (plan : InputsThrough fuel original initial) (fields : FieldsThrough fuel original initial)
          (request : NodeRequest Symbol Guard)
          (next : Value Symbol Guard → Code Symbol Guard Output) (before : Checked width)
          (used childFuel : Nat) (bounded : used + childFuel ≤ fuel) (smaller : childFuel < fuel)
          (origin : Steps used original initial
            (.code ((requestNode request.domain request.left request.right).bind next)) before)
          (nodes : Returned nodeLaw before.native.nodes)
          (edges : Returned edgeLaw before.native.edges) := by
        obtain ⟨_checked, childPhysical, _extension, childGrowth, childValid,
            _operationsGrowth, _boundInputs, childInputs, _boundFields, childFields⟩ :=
          SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
            fuel used original (.code (requestNode request.domain request.left request.right))
            next initial before sourceHeap physical plan fields valid sourceGrowth origin (by omega)
        have childPlan := through_mono (fuel - used) childFuel _ before (by omega) childInputs
        have childFieldPlan := fields_mono (fuel - used) childFuel _ before (by omega) childFields
        exact (ih childFuel smaller).1 request before childPhysical childGrowth childValid
          childPlan childFieldPlan nodes edges
      have edgeChild {Output : Type}
          (original : Control Output) (initial : Checked width)
          (physical : Physical initial.native)
          (sourceGrowth : Grows sourceHeap initial.native.machine.heap)
          (valid : SourceEqualityConstraintMemoAllocation.Valid initial.operations)
          (plan : InputsThrough fuel original initial) (fields : FieldsThrough fuel original initial)
          (request : EdgeRequest Symbol Guard)
          (next : EdgeValue Symbol Guard → Code Symbol Guard Output) (before : Checked width)
          (used childFuel : Nat) (bounded : used + childFuel ≤ fuel) (smaller : childFuel < fuel)
          (origin : Steps used original initial
            (.code ((requestEdge request.domain request.left request.right).bind next)) before)
          (nodes : Returned nodeLaw before.native.nodes)
          (edges : Returned edgeLaw before.native.edges) := by
        obtain ⟨_checked, childPhysical, _extension, childGrowth, childValid,
            _operationsGrowth, _boundInputs, childInputs, _boundFields, childFields⟩ :=
          SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
            fuel used original (.code (requestEdge request.domain request.left request.right))
            next initial before sourceHeap physical plan fields valid sourceGrowth origin (by omega)
        have childPlan := through_mono (fuel - used) childFuel _ before (by omega) childInputs
        have childFieldPlan := fields_mono (fuel - used) childFuel _ before (by omega) childFields
        exact (ih childFuel smaller).2 request before childPhysical childGrowth childValid
          childPlan childFieldPlan nodes edges
      have nodeRaw {Output : Type}
          (original : Control Output) (initial : Checked width)
          (physical : Physical initial.native)
          (sourceGrowth : Grows sourceHeap initial.native.machine.heap)
          (valid : SourceEqualityConstraintMemoAllocation.Valid initial.operations)
          (plan : InputsThrough fuel original initial) (fields : FieldsThrough fuel original initial)
          (past : ∀ used, used < fuel →
            Returned nodeLaw (execute used original initial).state.native.nodes ∧
            Returned edgeLaw (execute used original initial).state.native.edges)
          (child : NodeRequest Symbol Guard)
          (childNext : Value Symbol Guard → Code Symbol Guard Output)
          (childBefore childAfter : Checked width) (used count : Nat) (childValue : Value Symbol Guard)
          (positive : 0 < used) (bounded : used + count ≤ fuel)
          (origin : Steps used original initial
            (.code ((requestNode child.domain child.left child.right).bind childNext)) childBefore)
          (actual : Steps count (.code (requestNode child.domain child.left child.right)) childBefore
            (.code (.pure childValue)) childAfter) : nodeLaw child childValue := by
        cases count with
        | zero =>
            have impossible := Control.code.inj (steps_zero _ _ _ _ actual).1
            change (.node child .pure : Code Symbol Guard (Value Symbol Guard)) = .pure childValue at impossible
            cases impossible
        | succ count =>
            have previous := past used (by omega)
            have atPrefix : Returned nodeLaw childBefore.native.nodes ∧
                Returned edgeLaw childBefore.native.edges := by
              simpa only [origin.execute, Outcome.state] using previous
            have childResult := nodeChild original initial physical sourceGrowth valid plan fields child childNext childBefore
              used (count + 1) bounded (by omega) origin atPrefix.1 atPrefix.2
            exact childResult.2 (count + 1) childValue childAfter (by omega) actual
      have edgeRaw {Output : Type}
          (original : Control Output) (initial : Checked width)
          (physical : Physical initial.native)
          (sourceGrowth : Grows sourceHeap initial.native.machine.heap)
          (valid : SourceEqualityConstraintMemoAllocation.Valid initial.operations)
          (plan : InputsThrough fuel original initial) (fields : FieldsThrough fuel original initial)
          (past : ∀ used, used < fuel →
            Returned nodeLaw (execute used original initial).state.native.nodes ∧
            Returned edgeLaw (execute used original initial).state.native.edges)
          (child : EdgeRequest Symbol Guard)
          (childNext : EdgeValue Symbol Guard → Code Symbol Guard Output)
          (childBefore childAfter : Checked width) (used count : Nat) (childValue : EdgeValue Symbol Guard)
          (positive : 0 < used) (bounded : used + count ≤ fuel)
          (origin : Steps used original initial
            (.code ((requestEdge child.domain child.left child.right).bind childNext)) childBefore)
          (actual : Steps count (.code (requestEdge child.domain child.left child.right)) childBefore
            (.code (.pure childValue)) childAfter) : edgeLaw child childValue := by
        cases count with
        | zero =>
            have impossible := Control.code.inj (steps_zero _ _ _ _ actual).1
            change (.edge child .pure : Code Symbol Guard (EdgeValue Symbol Guard)) = .pure childValue at impossible
            cases impossible
        | succ count =>
            have previous := past used (by omega)
            have atPrefix : Returned nodeLaw childBefore.native.nodes ∧
                Returned edgeLaw childBefore.native.edges := by
              simpa only [origin.execute, Outcome.state] using previous
            have childResult := edgeChild original initial physical sourceGrowth valid plan fields child childNext childBefore
              used (count + 1) bounded (by omega) origin atPrefix.1 atPrefix.2
            exact childResult.2 (count + 1) childValue childAfter (by omega) actual
      constructor
      · intro request before physical sourceGrowth valid plan fields nodes edges
        have current := through_current fuel (.code (.node request .pure)) before plan
        have past (used : Nat) (smaller : used < fuel) :
            Returned nodeLaw (execute used (.code (.node request .pure)) before).state.native.nodes ∧
            Returned edgeLaw (execute used (.code (.node request .pure)) before).state.native.edges :=
          ((ih used smaller).1 request before physical sourceGrowth valid
            (through_mono fuel used _ before (by omega) plan)
            (fields_mono fuel used _ before (by omega) fields) nodes edges).1
        have bodyBundle : ∀ bodyFuel, bodyFuel < fuel →
            ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (first : Checked width),
            Steps 1 (.code (.node request .pure)) before
              (.code ((compileNode request).bind next)) first →
            Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
            Returned nodeLaw (execute bodyFuel (.code (compileNode request)) first).state.native.nodes ∧
            Returned edgeLaw (execute bodyFuel (.code (compileNode request)) first).state.native.edges ∧
            (∀ (value : Value Symbol Guard) (middle : Checked width),
              Steps bodyFuel (.code (compileNode request)) first (.code (.pure value)) middle →
              nodeLaw request value) := by
          intro bodyFuel smaller next first entered firstNodes firstEdges
          obtain ⟨_firstChecked, _firstPhysical, _firstExtension, firstGrowth, firstValid,
              _firstOperationsGrowth, _firstBoundInputs, _firstInputs, _firstBoundFields, _firstFields⟩ :=
            SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
              fuel 1 (.code (.node request .pure)) (.code (compileNode request)) next before first sourceHeap
              physical plan fields valid sourceGrowth entered (by omega)
          have preserved :=
            SourceCurrentAllocatedNativeBodyCodeReturned.body_code_returned_of_outer_query_induction
              nodeLaw edgeLaw (.code (.node request .pure)) before fuel
              (fun child childNext childBefore used childFuel _positive bounded small origin childNodes childEdges =>
                (nodeChild (.code (.node request .pure)) before physical sourceGrowth valid plan fields child childNext childBefore
                  used childFuel bounded small origin childNodes childEdges).1)
              (fun child childNext childBefore used childFuel _positive bounded small origin childNodes childEdges =>
                (edgeChild (.code (.node request .pure)) before physical sourceGrowth valid plan fields child childNext childBefore
                  used childFuel bounded small origin childNodes childEdges).1)
              (compileNode request) (compileNode_bodyCode request)
              next first 1 bodyFuel (by decide) (by omega) entered firstNodes firstEdges
          refine ⟨preserved.1, preserved.2, ?_⟩
          intro value middle actual
          exact nodeResults request before first middle fuel bodyFuel value next
            physical sourceGrowth valid plan fields entered firstGrowth firstValid smaller actual
            (by
              intro child childNext childBefore childAfter used count childValue positive bounded childEntry childTrace
              exact nodeRaw (.code (.node request .pure)) before physical sourceGrowth valid plan fields past
                child childNext childBefore childAfter used count childValue positive bounded childEntry childTrace)
            (by
              intro child childNext childBefore childAfter used count childValue positive bounded childEntry childTrace
              exact edgeRaw (.code (.node request .pure)) before physical sourceGrowth valid plan fields past
                child childNext childBefore childAfter used count childValue positive bounded childEntry childTrace)
        have preserved := SourceCurrentAllocatedNativeNodeQueryReturned.node_query_returned_of_body_induction
          nodeLaw edgeLaw request before fuel physical current.1 current.2 nodes edges bodyBundle
        refine ⟨preserved, ?_⟩
        intro count value after bounded actual
        apply SourceCurrentAllocatedNativeNodeQueryResult.node_query_result_of_body_induction
          nodeLaw request before after (count + 1) value physical current.1 current.2 nodes
          (trace_done count _ before after value actual)
        intro bodySteps shorter next first middle result entered bodyTrace
        have oneEndpoint := SourceCurrentAllocatedNativeNodeQueryReturned.node_query_returned_of_body_induction
          nodeLaw edgeLaw request before 1 physical current.1 current.2 nodes edges
          (fun bodyFuel small childNext childFirst origin childNodes childEdges =>
            bodyBundle bodyFuel (by omega) childNext childFirst origin childNodes childEdges)
        have firstLaws : Returned nodeLaw first.native.nodes ∧ Returned edgeLaw first.native.edges := by
          have firstRun := entered.execute
          simp only [requestNode] at firstRun
          simpa only [firstRun, Outcome.state] using oneEndpoint
        exact (bodyBundle bodySteps (by omega) next first entered firstLaws.1 firstLaws.2).2.2
          result middle bodyTrace
      · intro request before physical sourceGrowth valid plan fields nodes edges
        have current := through_current fuel (.code (.edge request .pure)) before plan
        have past (used : Nat) (smaller : used < fuel) :
            Returned nodeLaw (execute used (.code (.edge request .pure)) before).state.native.nodes ∧
            Returned edgeLaw (execute used (.code (.edge request .pure)) before).state.native.edges :=
          ((ih used smaller).2 request before physical sourceGrowth valid
            (through_mono fuel used _ before (by omega) plan)
            (fields_mono fuel used _ before (by omega) fields) nodes edges).1
        have bodyBundle : ∀ bodyFuel, bodyFuel < fuel →
            ∀ (next : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) (first : Checked width),
            Steps 1 (.code (.edge request .pure)) before (.edgeBody request next) first →
            Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
            Returned nodeLaw (execute bodyFuel (.edgeBody request .pure) first).state.native.nodes ∧
            Returned edgeLaw (execute bodyFuel (.edgeBody request .pure) first).state.native.edges ∧
            (∀ (value : EdgeValue Symbol Guard) (middle : Checked width),
              Steps bodyFuel (.edgeBody request .pure) first (.code (.pure value)) middle →
              edgeLaw request value) := by
          intro bodyFuel smaller next first entered firstNodes firstEdges
          obtain ⟨_firstChecked, _firstPhysical, _firstExtension, firstGrowth, firstValid,
              _firstOperationsGrowth, _firstBoundInputs, _firstInputs, _firstBoundFields, _firstFields⟩ :=
            SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
              fuel 1 (.code (.edge request .pure)) (.edgeBody request .pure) next before first sourceHeap
              physical plan fields valid sourceGrowth entered (by omega)
          have preserved := SourceCurrentAllocatedNativeEdgeBodyReturned.edge_body_returned_all_fuels
            nodeLaw edgeLaw request first bodyFuel firstNodes firstEdges (by
              intro used childFuel _positive bounded small pair _member childNext childBefore origin childNodes childEdges
              let joinedNext : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) :=
                fun value => (childNext value).bind next
              have lifted : Steps used (.edgeBody request next) first
                  (.code ((requestNode request.domain pair.1 pair.2).bind joinedNext)) childBefore := by
                simpa only [Control.bind, Code.bind, Code.bind_assoc, joinedNext] using origin.bind _ _ _ _ _ next
              have joined := entered.trans 1 used _ _ _ _ _ _ lifted
              exact (nodeChild (.code (.edge request .pure)) before physical sourceGrowth valid plan fields
                ⟨request.domain, pair.1, pair.2⟩ joinedNext childBefore (1 + used) childFuel
                (by omega) (Nat.lt_trans small smaller) joined childNodes childEdges).1)
          refine ⟨preserved.1, preserved.2, ?_⟩
          intro value middle actual
          exact edgeResults request before first middle fuel bodyFuel value next
            physical sourceGrowth valid plan fields entered firstGrowth firstValid smaller actual
            (by
              intro child childNext childBefore childAfter used count childValue positive bounded childEntry childTrace
              exact nodeRaw (.code (.edge request .pure)) before physical sourceGrowth valid plan fields past
                child childNext childBefore childAfter used count childValue positive bounded childEntry childTrace)
            (by
              intro child childNext childBefore childAfter used count childValue positive bounded childEntry childTrace
              exact edgeRaw (.code (.edge request .pure)) before physical sourceGrowth valid plan fields past
                child childNext childBefore childAfter used count childValue positive bounded childEntry childTrace)
        have preserved := SourceCurrentAllocatedNativeEdgeQueryReturned.edge_query_returned_of_body_induction
          nodeLaw edgeLaw request before fuel physical current.1 current.2 nodes edges bodyBundle
        refine ⟨preserved, ?_⟩
        intro count value after bounded actual
        apply SourceCurrentAllocatedNativeEdgeQueryResult.edge_query_result_of_body_induction
          edgeLaw request before after (count + 1) value physical current.1 current.2 edges
          (trace_done count _ before after value actual)
        intro bodySteps shorter next first middle result entered bodyTrace
        have oneEndpoint := SourceCurrentAllocatedNativeEdgeQueryReturned.edge_query_returned_of_body_induction
          nodeLaw edgeLaw request before 1 physical current.1 current.2 nodes edges
          (fun bodyFuel small childNext childFirst origin childNodes childEdges =>
            bodyBundle bodyFuel (by omega) childNext childFirst origin childNodes childEdges)
        have firstLaws : Returned nodeLaw first.native.nodes ∧ Returned edgeLaw first.native.edges := by
          have firstRun := entered.execute
          simp only [requestEdge] at firstRun
          simpa only [firstRun, Outcome.state] using oneEndpoint
        exact (bodyBundle bodySteps (by omega) next first entered firstLaws.1 firstLaws.2).2.2
          result middle bodyTrace

end MicroCFTA.SourceCurrentAllocatedNativeSourceQueryInduction
