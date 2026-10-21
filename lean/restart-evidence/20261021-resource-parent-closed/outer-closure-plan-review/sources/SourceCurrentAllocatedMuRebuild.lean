import MicroCFTA.SourceCurrentAllocatedNativeTraceEffects
import MicroCFTA.SourceCurrentConjunctionClassScan
import MicroCFTA.SourceEqualityMuReconstruction
import MicroCFTA.SourceEqualityProbeUnfold

/-!
# Filtered Mu probes through actual checked construction

The filtered-probe heap is separate from current semantic readiness.
Original construction derives it. Actual ordinary work and optional
binders preserve it. Checked execution follows its reached physical inputs.
A resident Mu then rebuilds by its cached probes at the unchanged heap.
This module does not infer filtered probes from readiness alone or prove
their transport through the complete outer caller.
-/
namespace MicroCFTA.SourceCurrentAllocatedMuRebuild
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap

/-- Actual original construction derives filtered probes for all stored Mu records. -/
theorem constructed {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    ProbeHeap heap := by
  simpa only [built, InternedNestedConstruction.Outcome.state] using
    InternedFreshOrdinaryProbeHeap.closed_heap expression

/-- Actual classified ordinary work retains the filtered probes of every stored record. -/
theorem work_heap {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (job : Work Symbol Guard Output) (heap : State Symbol Guard)
    (probes : ProbeHeap heap) (inputs : WorkInputs heap job) : ProbeHeap (run job heap).2 := by
  cases inputs with
  | pure => exact probes
  | edge => exact probes
  | node edges resident => exact InternedFreshOrdinaryProbeHeap.node edges heap probes
  | union values available => exact InternedFreshOrdinaryProbeHeap.union values heap probes

/-- Actual optional binding derives clean new probes from its literal stored-body plan. -/
theorem optionalBinder_heap {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (pair : Nat × Nat) (body : Value Symbol Guard) (heap : State Symbol Guard)
    (semantic : SemanticReady heap) (probes : ProbeHeap heap) (available : Available heap body) :
    ProbeHeap (SourceRecursiveIntersectionMaybeMu.maybeMu pair body heap).state := by
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair body heap heap
    semantic.ready.semantic.1.normal.facts available]
  split
  · exact InternedFreshOrdinaryProbeHeap.build_heap _ _ heap
      (SourceRecursiveIntersectionSemanticHeap.context heap semantic.ready.semantic _
        (InternedStoredSubstitution.leaves_available body heap available)) probes
  · exact probes

open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
variable {width : Nat}

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard Output) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

/-- Every actual checked instruction preserves filtered probes from its current physical inputs. -/
theorem step_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control Output) (state : Checked width)
    (semantic : SemanticReady state.native.machine.heap) (probes : ProbeHeap state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandHeap.Inputs control state) :
    ProbeHeap (step control state).state.native.machine.heap := by
  cases control with
  | edgeBody request next =>
      rw [step, SourceEqualityNativeDemandOperations.body_native]
      exact probes
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge => exact probes
      | work job next =>
          change ProbeHeap
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.work job next) state.native)).state.native.machine.heap
          rw [lift_heap]
          exact work_heap job state.native.machine.heap probes inputs
      | optionalBinder pair body next =>
          have retained := optionalBinder_heap pair body state.native.machine.heap semantic probes inputs
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state.native.machine.heap with
          | done value heap | pending key heap =>
              simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state, advance,
                InternedNestedConstruction.Outcome.state] using retained
      | node request next =>
          change ProbeHeap
            (lift state.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request next) state.native)).state.native.machine.heap
          rw [lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          exact probes
      | edge request next =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact probes

/-- Every finite checked outcome retains filtered probes along its actual reached inputs. -/
theorem execute_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : Checked width)
    (semantic : SemanticReady state.native.machine.heap) (probes : ProbeHeap state.native.machine.heap)
    (inputs : SourceEqualityNativeDemandHeap.InputsThrough fuel control state) :
    ProbeHeap (execute fuel control state).state.native.machine.heap := by
  induction fuel generalizing control state with
  | zero => exact probes
  | succ fuel ih =>
      have one := step_heap control state semantic probes inputs.1
      have oneSemantic := SourceCurrentAllocatedNativeSemanticHeap.step_semantic control state semantic inputs.1
      cases actual : step control state with
      | yielded next after =>
          have nextProbes : ProbeHeap after.native.machine.heap := by
            simpa only [actual, Outcome.state] using one
          have nextSemantic : SemanticReady after.native.machine.heap := by
            simpa only [actual, Outcome.state] using oneSemantic
          have nextInputs : SourceEqualityNativeDemandHeap.InputsThrough fuel next after := by
            simpa only [SourceEqualityNativeDemandHeap.InputsThrough, actual] using inputs.2
          simpa only [execute, actual] using ih next after nextSemantic nextProbes nextInputs
      | done | failed | constraintError | blocked =>
          simpa only [execute, actual, Outcome.state] using one

/-- The existing physical plan supplies the reached primitive checks without a semantic result law. -/
theorem execute_heap_of_physical [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (state : Checked width)
    (semantic : SemanticReady state.native.machine.heap) (probes : ProbeHeap state.native.machine.heap)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel control state) :
    ProbeHeap (execute fuel control state).state.native.machine.heap :=
  execute_heap fuel control state semantic probes
    (SourceCurrentAllocatedNativePhysicalExecution.through_heap fuel control state inputs)

/-- An actual completed physical trace derives the final probe heap from its own reached checks. -/
theorem trace_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control : Control Output} {before after : Checked width} {value : Output}
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel control before (.code (.pure value)) after)
    (semantic : SemanticReady before.native.machine.heap) (probes : ProbeHeap before.native.machine.heap) :
    ProbeHeap after.native.machine.heap := by
  have done := trace_done fuel control before after value trace.steps
  simpa only [done, Outcome.state] using execute_heap_of_physical (fuel + 1) control before semantic probes trace.plan

/-- Resident filtered probes derive the exact source reconstruction at the same full native state. -/
theorem resident_rebuild [DecidableEq (EdgeKey Symbol Guard)]
    (before : Checked width) (ready : Ready before) (probes : ProbeHeap before.native.machine.heap)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available before.native.machine.heap (.mu entry body depth ordinary)) :
    SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.native.machine.heap =
        .done (cleanup (.mu entry body depth ordinary)) before.native.machine.heap ∧
      Available before.native.machine.heap (cleanup (.mu entry body depth ordinary)) ∧
      (cleanup (.mu entry body depth ordinary)).free = (Value.mu entry body depth ordinary).free ∧
      ∀ (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol),
        InternedGuardedLanguage.meaning holds ambient (cleanup (.mu entry body depth ordinary)) =
          InternedGuardedLanguage.meaning holds ambient (.mu entry body depth ordinary) := by
  have clean := InternedFreshOrdinaryProbeHeap.resident before.native.machine.heap probes entry body depth ordinary available
  have coherent := ready.semantic.ready.semantic.1.normal.facts.coherent
  exact ⟨SourceEqualityMuReconstruction.completed entry body depth ordinary before.native.machine.heap coherent available clean,
    InternedConstructionProvenance.cleanup_available _ available,
    InternedNormalizationFree.cleanup_free _, fun holds ambient =>
      InternedGuardedLanguage.cleanup_exact holds ambient _ before.native.machine.heap coherent available⟩

/-- The actual raw binder branch has the derived cleanup result and unchanged heap. -/
theorem actual_rebuild [DecidableEq (EdgeKey Symbol Guard)]
    (before : Checked width) (ready : Ready before) (probes : ProbeHeap before.native.machine.heap)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available before.native.machine.heap (.mu entry body depth ordinary))
    (result : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.native.machine.heap = .done result heap) :
    result = cleanup (.mu entry body depth ordinary) ∧ heap = before.native.machine.heap := by
  have completed := (resident_rebuild before ready probes entry body depth ordinary available).1
  exact InternedNestedConstruction.Outcome.done.inj (actual.symm.trans completed)

end MicroCFTA.SourceCurrentAllocatedMuRebuild
