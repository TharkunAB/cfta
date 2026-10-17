import MicroCFTA.SourceCurrentNativeMuHistory
import MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap

/-!
# Causal Mu publication histories through checked native execution

Physical constructor inputs derive histories for each actual heap change.
Native memo controls and protected finish frames retain the same heap.
The trace producer constructs the reached history from the initial history.
It assumes no future callback law or completed query.
-/
namespace MicroCFTA.SourceCurrentNativePublicationTrace
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedShallowHeap (NoNewMu noNewMu_refl)
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)
open SourceCurrentNativeMuPublication (History)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Every physically admitted primitive Work job adds no completed Mu record. -/
theorem work_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard Result)
    (before : State Symbol Guard) (inputs : WorkInputs before job) :
    NoNewMu before (run job before).2 := by
  cases inputs with
  | pure => exact noNewMu_refl before
  | edge => exact noNewMu_refl before
  | node rows => exact InternedShallowHeap.makeNode_noNewMu rows before
  | union values => exact InternedShallowHeap.makeUnion_noNewMu values before

/-- An actual primitive job has a causal history without a semantic output premise. -/
theorem work [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard Result)
    (before : State Symbol Guard) (inputs : WorkInputs before job) :
    Nonempty (History before (run job before).2) :=
  ⟨.retain before _ (work_noNewMu job before inputs)⟩

private theorem work_semantic [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard Result)
    (before : State Symbol Guard) (semantic : SemanticHeap before) (inputs : WorkInputs before job) :
    SemanticHeap (run job before).2 := by
  cases inputs with
  | pure => exact semantic
  | edge symbol guard values available =>
      exact SourceRecursiveIntersectionSemanticHeap.edge symbol guard values before semantic available
  | node rows resident => exact SourceRecursiveIntersectionSemanticHeap.node rows before semantic resident
  | union values available => exact SourceRecursiveIntersectionSemanticHeap.union values before semantic available

open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "HeapInputs" => SourceEqualityNativeDemandHeap.Inputs
local notation "Trace" => SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace
variable {A : Type} {width fuel : Nat}

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- One actual checked instruction constructs its stopping history on every outcome. -/
theorem step (control : Control A) (before : Checked width)
    (semantic : SemanticHeap before.native.machine.heap) (inputs : HeapInputs control before) :
    SemanticHeap (SourceEqualityNativeDemand.step control before).state.native.machine.heap ∧
      Nonempty (History before.native.machine.heap
        (SourceEqualityNativeDemand.step control before).state.native.machine.heap) := by
  cases control with
  | edgeBody request next =>
      rw [SourceEqualityNativeDemand.step, SourceEqualityNativeDemandOperations.body_native]
      exact ⟨semantic, ⟨.refl _⟩⟩
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact ⟨semantic, ⟨.refl _⟩⟩
      | work job next =>
          change SemanticHeap
              (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
                SourceEqualityPCSNativeEdge.conjoin (.work job next) before.native)).state.native.machine.heap ∧ _
          rw [lift_heap]
          exact ⟨work_semantic job before.native.machine.heap semantic inputs,
            work job before.native.machine.heap inputs⟩
      | optionalBinder pair body next =>
          have retained := SourceRecursiveIntersectionSemanticHeap.optionalBinder pair body before.native.machine.heap semantic inputs
          have history := SourceCurrentNativeMuHistory.maybeMu pair body before.native.machine.heap semantic inputs
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
          | done value heap | pending key heap =>
              simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, actual,
                lift, Outcome.state, advance, InternedNestedConstruction.Outcome.state] using And.intro retained history
      | node request next =>
          change SemanticHeap
              (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
                SourceEqualityPCSNativeEdge.conjoin (.node request next) before.native)).state.native.machine.heap ∧ _
          rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          refine ⟨semantic, ?_⟩
          change Nonempty (History before.native.machine.heap
            (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) before.native)).state.native.machine.heap)
          rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          exact ⟨.refl _⟩
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact ⟨semantic, ⟨.refl _⟩⟩

/-- A physically admitted yielded trace constructs its own reached publication history. -/
theorem trace {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after) (semantic : SemanticHeap before.native.machine.heap) :
    SemanticHeap after.native.machine.heap ∧ Nonempty (History before.native.machine.heap after.native.machine.heap) := by
  induction actual with
  | refl => exact ⟨semantic, ⟨.refl _⟩⟩
  | cons control before middle current rest after count inputs one tail ih =>
      have checked := step control before semantic
        (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs)
      have reached : SemanticHeap current.native.machine.heap ∧
          Nonempty (History before.native.machine.heap current.native.machine.heap) := by
        simpa only [one, Outcome.state] using checked
      obtain ⟨laterSemantic, ⟨laterHistory⟩⟩ := ih reached.1
      obtain ⟨oneHistory⟩ := reached.2
      exact ⟨laterSemantic, ⟨.trans oneHistory laterHistory⟩⟩

/-- Every bounded actual outcome retains its complete causal history, including faults and blocked states. -/
theorem execute (count : Nat) (control : Control A) (before : Checked width)
    (semantic : SemanticHeap before.native.machine.heap)
    (inputs : SourceEqualityNativeDemandHeap.InputsThrough count control before) :
    SemanticHeap (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap ∧
      Nonempty (History before.native.machine.heap
        (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap) := by
  induction count generalizing control before with
  | zero => exact ⟨semantic, ⟨.refl _⟩⟩
  | succ count ih =>
      have checked := step control before semantic inputs.1
      cases actual : SourceEqualityNativeDemand.step control before with
      | yielded next after =>
          have reached : SemanticHeap after.native.machine.heap ∧
              Nonempty (History before.native.machine.heap after.native.machine.heap) := by
            simpa only [actual, Outcome.state] using checked
          have remaining : SourceEqualityNativeDemandHeap.InputsThrough count next after := by
            simpa only [SourceEqualityNativeDemandHeap.InputsThrough, actual] using inputs.2
          obtain ⟨laterSemantic, ⟨laterHistory⟩⟩ := ih next after reached.1 remaining
          obtain ⟨oneHistory⟩ := reached.2
          simpa only [SourceEqualityNativeDemand.execute, actual] using
            And.intro laterSemantic (Nonempty.intro (History.trans oneHistory laterHistory))
      | done | failed | constraintError | blocked =>
          simpa only [SourceEqualityNativeDemand.execute, actual, Outcome.state] using checked

/-- A warm trace extends its actual prior source history without replacing any native table. -/
theorem from_history {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after) (semantic : SemanticHeap before.native.machine.heap)
    (earlier : History empty before.native.machine.heap) :
    SemanticHeap after.native.machine.heap ∧ Nonempty (History empty after.native.machine.heap) := by
  obtain ⟨retained, ⟨history⟩⟩ := trace actual semantic
  exact ⟨retained, ⟨.trans earlier history⟩⟩

/-- Actual initial source construction supplies the semantic heap and publication history internally. -/
theorem source_trace (source : InternedNestedConstruction.Syntax Symbol Guard)
    {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after)
    (initial : before.native.machine.heap =
      (InternedFreshOrdinaryConstruction.build source [] empty).state) :
    SemanticHeap after.native.machine.heap ∧ Nonempty (History empty after.native.machine.heap) := by
  have semantic : SemanticHeap before.native.machine.heap := by
    rw [initial]
    exact SourceRecursiveIntersectionSemanticHeap.source source [] empty
      SourceRecursiveIntersectionSemanticHeap.empty_heap (by intro value member; cases member)
  have earlier : History empty before.native.machine.heap := by
    rw [initial]
    exact SourceCurrentNativeMuPublication.closed_history source
  exact from_history actual semantic earlier

/-- Every reached selected Mu derives unused smart readback from its actual first-writer history. -/
theorem reached_unused {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after) (semantic : SemanticHeap before.native.machine.heap)
    (earlier : History empty before.native.machine.heap)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary))
    (unused : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false) :
    InternedNestedConstruction.finish true (.mu entry body depth ordinary) =
      SourceCurrentNativeCallbackErasure.eraseSelf
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary := by
  obtain ⟨_, ⟨history⟩⟩ := from_history actual semantic earlier
  exact SourceCurrentNativeNormalizedComparisonExecution.history_unused _ history key entry body depth ordinary present unused

/-- A source-started checked trace establishes the stored law without a supplied semantic or callback law. -/
theorem source_unused (source : InternedNestedConstruction.Syntax Symbol Guard)
    {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after)
    (initial : before.native.machine.heap =
      (InternedFreshOrdinaryConstruction.build source [] empty).state)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary))
    (unused : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false) :
    InternedNestedConstruction.finish true (.mu entry body depth ordinary) =
      SourceCurrentNativeCallbackErasure.eraseSelf
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary := by
  obtain ⟨_, ⟨history⟩⟩ := source_trace source actual initial
  exact SourceCurrentNativeNormalizedComparisonExecution.history_unused _ history key entry body depth ordinary present unused

end MicroCFTA.SourceCurrentNativePublicationTrace
