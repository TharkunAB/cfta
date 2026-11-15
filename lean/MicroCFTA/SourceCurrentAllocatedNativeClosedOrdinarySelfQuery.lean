import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryResult
import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryReturned
import MicroCFTA.SourceCurrentAllocatedNativeResetSwapBodyReturned
import MicroCFTA.SourceCurrentNativeEnterCommonOperand

/-!
# Literal ordinary operand at an actual closed-self query

The prior returned law concerns only the original and reset requests.
The actual physical trace supplies dispatch readiness and word bounds.
Self returns before repeated-pair lookup, including after the real reset.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeClosedOrdinarySelfQuery
open Cache InternedConstructorTemplates InternedBinderProtocol InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "Through" => SourceCurrentAllocatedNativePhysicalExecution.InputsThrough
local notation "Trace" => SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace
variable {width : Nat}

set_option autoImplicit false

private theorem true_returned {Key Request Answer : Type}
    (state : FlatMemoThunk.State Key Request Answer) : Returned (fun _ _ => True) state := by
  intro handle request value stored
  trivial

private theorem pure_state
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : Checked width) :
    (SourceEqualityNativeDemand.execute fuel (.code (.pure value)) state).state = state := by
  cases fuel <;> rfl

private theorem through_head
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control (Value Symbol Guard)) (state : Checked width)
    (plan : Through fuel control state) : Inputs control state := by
  cases fuel with
  | zero => exact plan
  | succ fuel => exact plan.1

private theorem one_step
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control (Value Symbol Guard)) (before after : Checked width)
    (actual : Steps 1 control before next after) :
    SourceEqualityNativeDemand.step control before = .yielded next after := by
  obtain ⟨rest, middle, one, tail⟩ := steps_succ 0 _ _ _ _ actual
  obtain ⟨sameControl, sameState⟩ := steps_zero _ _ _ _ tail
  simpa only [sameControl, sameState] using one

private theorem self_compile [DecidableEq Symbol]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (entry : Interned NodeKey)
    (rows : List (EdgeValue Symbol Guard)) (level : Nat)
    (emptyFree : domain.key.free.isEmpty = true) :
    compileNode ⟨domain, .node entry rows level [], .node entry rows level []⟩ =
      .pure (.node entry rows level []) := by
  simp [compileNode, SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
    SourceRecursiveIntersectionControl.reset, SourceRecursiveIntersectionControl.closedSelf,
    Value.referenceOf, Value.free, emptyFree]

private theorem reset_selected
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (entry : Interned NodeKey)
    (rows : List (EdgeValue Symbol Guard)) (level : Nat)
    (nonemptyFree : domain.key.free.isEmpty = false) :
    SourceRecursiveIntersectionControl.decision domain.key
      (.node entry rows level []) (.node entry rows level []) = .reset := by
  simp [SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
    SourceRecursiveIntersectionControl.reset, Value.referenceOf, Value.free, nonemptyFree]

/-- Actual pure source bodies establish their cache law at every query budget and pure endpoint. -/
private theorem terminal_query_laws
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (law : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (state : Checked width) (operand : Value Symbol Guard)
    (physical : Physical state.native) (ready : NodeReady state.native.machine request)
    (safe : ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (returned : Returned law state.native.nodes)
    (compiled : compileNode request = .pure operand) (bodyLaw : law request operand) :
    (∀ fuel, Returned law (SourceEqualityNativeDemand.execute fuel
      (.code (.node request .pure)) state).state.native.nodes) ∧
    (∀ steps (value : Value Symbol Guard) (after : Checked width),
      Steps steps (.code (.node request .pure)) state (.code (.pure value)) after → law request value) := by
  have completed : ∀ fuel (value : Value Symbol Guard) (after : Checked width),
      SourceEqualityNativeDemand.execute fuel (.code (.node request .pure)) state = .done value after →
      law request value := by
    intro fuel value after done
    apply SourceCurrentAllocatedNativeNodeQueryResult.node_query_result_of_body_induction
      law request state after fuel value physical ready safe returned done
    intro bodySteps bounded next first middle result origin actualBody
    rw [compiled] at actualBody
    have same := (pure_trace bodySteps operand result first middle actualBody).2.1
    simpa only [← same] using bodyLaw
  constructor
  · intro fuel
    have both := SourceCurrentAllocatedNativeNodeQueryReturned.node_query_returned_of_body_induction
      law (fun _ _ => True) request state fuel physical ready safe returned (true_returned state.native.edges)
      (by
        intro bodyFuel smaller next first origin firstNodes firstEdges
        refine ⟨?_, ?_, ?_⟩
        · simpa only [compiled, pure_state] using firstNodes
        · simpa only [compiled, pure_state] using firstEdges
        · intro value middle actualBody
          rw [compiled] at actualBody
          have same := (pure_trace bodyFuel operand value first middle actualBody).2.1
          simpa only [← same] using bodyLaw)
    exact both.1
  · intro steps value after actual
    exact completed (steps + 1) value after (trace_done steps _ state after value actual)

/-- The actual ordinary self query returns its original record, including warm and reset cases. -/
theorem closed_ordinary_self_query_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (entry : Interned NodeKey)
    (rows : List (EdgeValue Symbol Guard)) (level : Nat)
    (before after : Checked width) (fuel traceSteps : Nat) (value : Value Symbol Guard)
    (physical : Physical before.native)
    (returned :
      let operand : Value Symbol Guard := .node entry rows level []
      Returned (fun request result =>
        (request = ⟨domain, operand, operand⟩ ∨
          request = ⟨IntersectionEmptyDomain.emptyDomain, operand, operand⟩) → result = operand)
        before.native.nodes)
    (actual :
      let operand : Value Symbol Guard := .node entry rows level []
      Trace traceSteps (.code (requestNode domain operand operand)) before (.code (.pure value)) after)
    (done :
      let operand : Value Symbol Guard := .node entry rows level []
      SourceEqualityNativeDemand.execute fuel (.code (requestNode domain operand operand)) before =
        .done value after) :
    value = .node entry rows level [] ∧ Physical after.native ∧
      Extension before.native.machine after.native.machine ∧ Available after.native.machine.heap value := by
  let operand : Value Symbol Guard := .node entry rows level []
  let request : NodeRequest Symbol Guard := ⟨domain, operand, operand⟩
  let emptyRequest : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, operand, operand⟩
  let law : NodeRequest Symbol Guard → Value Symbol Guard → Prop :=
    fun queried result => (queried = request ∨ queried = emptyRequest) → result = operand
  change Returned law before.native.nodes at returned
  change Trace traceSteps (.code (.node request .pure)) before (.code (.pure value)) after at actual
  change SourceEqualityNativeDemand.execute fuel (.code (.node request .pure)) before = .done value after at done
  have plan : Through (traceSteps + 1) (.code (.node request .pure)) before := actual.plan
  have parentInputs : Inputs (.code (.node request .pure)) before := plan.1
  have parentReady : NodeReady before.native.machine request := parentInputs.1
  have parentSafe : ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right := parentInputs.2
  have lawOperand : ∀ queried, law queried operand := by intro queried qualifies; rfl
  have valueEq : value = operand := by
    cases emptyFree : domain.key.free.isEmpty with
    | true =>
        have compiled : compileNode request = .pure operand := self_compile domain entry rows level emptyFree
        have resultLaw := SourceCurrentAllocatedNativeNodeQueryResult.node_query_result_of_body_induction
          law request before after fuel value physical parentReady parentSafe returned done
          (by
            intro bodySteps bounded next first middle result origin actualBody
            rw [compiled] at actualBody
            have same := (pure_trace bodySteps operand result first middle actualBody).2.1
            simpa only [← same] using lawOperand request)
        exact resultLaw (.inl rfl)
    | false =>
        have chosen := reset_selected domain entry rows level emptyFree
        have compiled : compileNode request = requestNode emptyRequest.domain emptyRequest.left emptyRequest.right := by
          simp only [request, emptyRequest, operand, compileNode, chosen]
        have emptyCompiled : compileNode emptyRequest = .pure operand :=
          self_compile IntersectionEmptyDomain.emptyDomain entry rows level rfl
        have dispatchLaws := SourceCurrentAllocatedNativeNodeQueryReturned.node_query_returned_of_body_induction
          law (fun _ _ => True) request before 1 physical parentReady parentSafe returned
          (true_returned before.native.edges)
          (by
            intro bodyFuel smaller next first origin firstNodes firstEdges
            have zero : bodyFuel = 0 := by omega
            subst bodyFuel
            refine ⟨firstNodes, firstEdges, ?_⟩
            intro result middle actualBody
            have same := Control.code.inj (steps_zero _ _ _ _ actualBody).1
            rw [compiled] at same
            cases same)
        have resultLaw := SourceCurrentAllocatedNativeNodeQueryResult.node_query_result_of_body_induction
          law request before after fuel value physical parentReady parentSafe returned done
          (by
            intro bodySteps bounded next first middle result origin actualBody
            have one : SourceEqualityNativeDemand.step (.code (.node request .pure)) before =
                .yielded (.code ((compileNode request).bind next)) first :=
              one_step _ _ before first origin
            have firstPhysical : Physical first.native := by
              have checked := SourceCurrentAllocatedNativePhysicalExecution.step_valid
                (.code (.node request .pure)) before physical parentInputs
              simpa only [one, Outcome.state] using checked
            have firstReturned : Returned law first.native.nodes := by
              simpa only [SourceEqualityNativeDemand.execute, one, Outcome.state] using dispatchLaws.1
            have firstPlan : Through traceSteps (.code ((compileNode request).bind next)) first := by
              have laterPlan := plan.2
              rw [one] at laterPlan
              exact laterPlan
            have firstInputs := through_head traceSteps _ first firstPlan
            have childInputs : NodeReady first.native.machine emptyRequest ∧
                (∀ key, SourceRecursiveIntersectionMemo.requestKey width emptyRequest.domain emptyRequest.left emptyRequest.right = some key →
                  SourceRecursiveIntersectionMemo.KeySafe width emptyRequest.domain emptyRequest.left emptyRequest.right) := by
              simpa only [compiled, requestNode, Code.bind, SourceCurrentAllocatedNativePhysicalExecution.Inputs,
                emptyRequest] using firstInputs
            obtain ⟨_child, _branch, _compiled, _childOrigin, bodyLaws⟩ :=
              SourceCurrentAllocatedNativeResetSwapBodyReturned.reset_swap_body_of_outer_query_induction
                law (fun _ _ => True) (fun result => result = operand)
                request before first fuel next (.inl chosen) origin firstReturned (true_returned first.native.edges)
                (by
                  intro child branch childFuel shorter childOrigin childNodes childEdges
                  rcases branch with reset | swap
                  · have sameChild : child = emptyRequest := reset.2
                    subst child
                    have terminal := terminal_query_laws law emptyRequest first operand
                      firstPhysical childInputs.1 childInputs.2 childNodes emptyCompiled (lawOperand emptyRequest)
                    refine ⟨terminal.1 childFuel, true_returned _, ?_⟩
                    intro observed final childActual
                    exact (terminal.2 childFuel observed final childActual) (.inr rfl)
                  · have impossible := chosen.symm.trans swap.1
                    cases impossible)
            have exactResult := (bodyLaws bodySteps (by omega)).2.2.1 bodySteps (Nat.le_refl _) result middle actualBody
            intro qualifies
            exact exactResult)
        exact resultLaw (.inl rfl)
  have retained := SourceCurrentNativeEnterCommonOperand.checked_trace_extension actual physical
  have valueAvailable : Available after.native.machine.heap value := by
    rw [valueEq]
    exact retained.2.available operand parentReady.2.1
  exact ⟨valueEq, retained.1, retained.2, valueAvailable⟩

end MicroCFTA.SourceCurrentAllocatedNativeClosedOrdinarySelfQuery
