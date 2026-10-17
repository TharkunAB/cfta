import MicroCFTA.SourceCurrentRequiredUnionNormal
import MicroCFTA.SourceCurrentConstrainedCapNativeGuardHeap
import MicroCFTA.SourceCurrentAllocatedTargetQuery

/-!
# Union normality through actual checked native execution

The invariant follows every literal source write. Optional binders use
repaired stored execution on all stopping outcomes. Physical instruction
checks restrict arbitrary Work programs to the actual source constructors.
No closure, cap, or future returned-heap premise is required.
-/
namespace MicroCFTA.SourceCurrentRequiredUnionNormalNative
open InternedConstructorTemplates
open InternedNestedConstruction (Outcome work)
open InternedBinderProtocol (Reference)
open SourceCurrentRequiredUnionNormal (UnionNormal)

private theorem bind (outcome : Outcome Symbol Guard A)
    (next : A → State Symbol Guard → Outcome Symbol Guard B)
    (normal : UnionNormal outcome.state)
    (later : ∀ value after, outcome = .done value after → UnionNormal after → UnionNormal (next value after).state) :
    UnionNormal (outcome.bind next).state := by
  cases outcome with
  | pending => exact normal
  | done value after => exact later value after rfl normal

/-- Actual substitution and self-reference filtering retain every earlier union record. -/
theorem callback [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (name : Reference) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceRecursiveIntersectionMaybeMu.callback old body name state).state := by
  unfold SourceRecursiveIntersectionMaybeMu.callback
  exact bind _ _ (SourceCurrentRequiredUnionNormal.execute body _ state normal)
    (fun value after _ afterNormal => SourceCurrentRequiredUnionNormal.filter name value after afterNormal)

/-- Both probes and the exact first-writer Mu request retain the invariant. -/
theorem construct [DecidableEq (EdgeKey Symbol Guard)] (old : Reference) (body : Value Symbol Guard)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceRecursiveIntersectionMaybeMu.construct old body state).state := by
  unfold SourceRecursiveIntersectionMaybeMu.construct
  apply bind _ _ (callback old body .depth state normal)
  intro depth afterDepth _ depthNormal
  apply bind _ _ (callback old body (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthNormal)
  intro ordinary afterOrdinary _ ordinaryNormal
  exact SourceCurrentRequiredUnionNormal.request true depth ordinary _ afterOrdinary ordinaryNormal
    (fun name current currentNormal => callback old body name current currentNormal)

/-- An optional binder retains union normality on used, unused, and pending branches. -/
theorem optional [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state := by
  unfold SourceRecursiveIntersectionMaybeMu.maybeMu
  split
  · exact construct _ body state normal
  · exact normal

/-- Every physically admitted primitive writes only source constructor payloads. -/
theorem work_normal [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard A)
    (state : State Symbol Guard) (inputs : SourceEqualityNativeDemandHeapPrimitives.WorkInputs state job)
    (normal : UnionNormal state) : UnionNormal (run job state).2 := by
  cases inputs with
  | pure => exact normal
  | edge symbol guard values available => exact SourceCurrentRequiredUnionNormal.edge symbol guard values state normal
  | node edges resident => exact SourceCurrentRequiredUnionNormal.node edges state normal
  | union values available => exact SourceCurrentRequiredUnionNormal.union values state normal

section Current
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat}

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

/-- One actual checked instruction retains the same heap invariant at every stopping outcome. -/
theorem step_normal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (state : SourceEqualityNativeDemand.State width)
    (inputs : SourceEqualityNativeDemandHeap.Inputs control state)
    (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (step control state).state.native.machine.heap := by
  cases control with
  | edgeBody request next =>
      rw [step, SourceEqualityNativeDemandOperations.body_native]
      exact normal
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact normal
      | work job next =>
          change UnionNormal
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.work job next) state.native)).state.native.machine.heap
          rw [lift_heap]
          exact work_normal job state.native.machine.heap inputs normal
      | optionalBinder pair body next =>
          have retained := optional pair body state.native.machine.heap normal
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.native.machine.heap with
          | done value after | pending key after =>
              simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift,
                SourceEqualityNativeDemand.Outcome.state, SourceRecursiveIntersectionThunks.advance, Outcome.state] using retained
      | node request next =>
          change UnionNormal
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) state.native)).state.native.machine.heap
          rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          exact normal
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact normal

/-- The bounded checked interpreter retains the invariant on success and every failure. -/
theorem execute_normal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (state : SourceEqualityNativeDemand.State width)
    (inputs : SourceEqualityNativeDemandHeap.InputsThrough fuel control state)
    (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceEqualityNativeDemand.execute fuel control state).state.native.machine.heap := by
  induction fuel generalizing control state with
  | zero => exact normal
  | succ fuel ih =>
      have retained := step_normal control state inputs.1 normal
      cases actual : step control state with
      | yielded next after =>
          have afterNormal : UnionNormal after.native.machine.heap := by
            simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using retained
          have nextInputs : SourceEqualityNativeDemandHeap.InputsThrough fuel next after := by
            simpa only [actual] using inputs.2
          simpa only [SourceEqualityNativeDemand.execute, actual] using ih next after nextInputs afterNormal
      | done | failed | constraintError | blocked =>
          simpa only [SourceEqualityNativeDemand.execute, actual, SourceEqualityNativeDemand.Outcome.state] using retained

private theorem physical_inputs [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (state : SourceEqualityNativeDemand.State width)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control state) :
    SourceEqualityNativeDemandHeap.Inputs control state := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact inputs | trivial

/-- An actual physical native prefix retains union normality at its exact returned state. -/
theorem trace_normal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control remaining : Control A} {before after : SourceEqualityNativeDemand.State width}
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel control before remaining after)
    (normal : UnionNormal before.native.machine.heap) : UnionNormal after.native.machine.heap := by
  induction trace with
  | refl => exact normal
  | cons control state next middle final result fuel inputs actual rest ih =>
      have retained := step_normal control state (physical_inputs control state inputs) normal
      exact ih (by simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using retained)

/-- The same actual allocated native query retains the source-derived union invariant. -/
theorem query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {left right result : Value Symbol Guard} {before after : SourceEqualityNativeDemand.State width}
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after)
    (normal : UnionNormal before.native.machine.heap) : UnionNormal after.native.machine.heap := by
  cases actual with
  | run trace => exact trace_normal trace normal
end Current
end MicroCFTA.SourceCurrentRequiredUnionNormalNative
