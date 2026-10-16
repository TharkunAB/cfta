import MicroCFTA.SourceCurrentAllocatedMuRebuild
import MicroCFTA.SourceCurrentAllocatedPartialGraph

namespace MicroCFTA.SourceCurrentAllocatedMuRebuild
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityNativeDemandHeapPrimitives (WorkInputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap

#print axioms constructed
#print axioms work_heap
#print axioms optionalBinder_heap
#print axioms step_heap
#print axioms execute_heap
#print axioms execute_heap_of_physical
#print axioms trace_heap
#print axioms resident_rebuild
#print axioms actual_rebuild

#check @constructed
#check @work_heap
#check @optionalBinder_heap
#check @step_heap
#check @execute_heap
#check @execute_heap_of_physical
#check @trace_heap
#check @resident_rebuild
#check @actual_rebuild

variable {width : Nat}

/-- Original construction derives both probes without a future heap premise. -/
theorem kernel_original [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) : ProbeHeap heap :=
  constructed expression value heap built

/-- Ordinary edge interning needs no semantic or closed-whole-forest premise to retain probes. -/
theorem kernel_raw_edge [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (heap : InternedConstructorTemplates.State Symbol Guard) (probes : ProbeHeap heap)
    (available : InternedNestedProvenance.Values heap values) :
    ProbeHeap (run (makeEdge symbol guard values) heap).2 :=
  work_heap (makeEdge symbol guard values) heap probes (.edge symbol guard values available)

/-- Optional binding preserves the heap for arbitrary available bodies, including open ones. -/
theorem kernel_optional [DecidableEq (EdgeKey Symbol Guard)]
    (pair : Nat × Nat) (body : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SemanticReady heap) (probes : ProbeHeap heap) (available : Available heap body) :
    ProbeHeap (SourceRecursiveIntersectionMaybeMu.maybeMu pair body heap).state :=
  optionalBinder_heap pair body heap semantic probes available

/-- A finite checked observation retains probes without a completed-result premise. -/
theorem kernel_finite_observation [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control Output) (before : Checked width)
    (semantic : SemanticReady before.native.machine.heap) (probes : ProbeHeap before.native.machine.heap)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough fuel control before) :
    ProbeHeap (execute fuel control before).state.native.machine.heap :=
  execute_heap_of_physical fuel control before semantic probes inputs

/-- The actual physical trace supplies every reached check used for the returned heap. -/
theorem kernel_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {fuel : Nat} {control : Control Output} {before after : Checked width} {value : Output}
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel control before (.code (.pure value)) after)
    (semantic : SemanticReady before.native.machine.heap) (probes : ProbeHeap before.native.machine.heap) :
    ProbeHeap after.native.machine.heap := trace_heap trace semantic probes

/-- The resident endpoint has exact all-guard meaning and preserves the cached free list. -/
theorem kernel_rebuild_language [DecidableEq (EdgeKey Symbol Guard)]
    (before : Checked width) (ready : Ready before) (probes : ProbeHeap before.native.machine.heap)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available before.native.machine.heap (.mu entry body depth ordinary))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) :
    (cleanup (.mu entry body depth ordinary)).free = (Value.mu entry body depth ordinary).free ∧
      InternedGuardedLanguage.meaning holds ambient (cleanup (.mu entry body depth ordinary)) =
        InternedGuardedLanguage.meaning holds ambient (.mu entry body depth ordinary) := by
  have receipt := resident_rebuild before ready probes entry body depth ordinary available
  exact ⟨receipt.2.2.1, receipt.2.2.2 holds ambient⟩

/-- The actual rebuild return advances the same whole checked state. -/
theorem kernel_checked_unchanged [DecidableEq (EdgeKey Symbol Guard)]
    (before : Checked width) (ready : Ready before) (probes : ProbeHeap before.native.machine.heap)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available before.native.machine.heap (.mu entry body depth ordinary))
    (result : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard)
    (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.native.machine.heap = .done result heap) :
    SourceCurrentAllocatedQueryMemo.advancePhysical before ⟨heap, before.operations⟩ = before := by
  have same := (actual_rebuild before ready probes entry body depth ordinary available result heap actual).2
  rw [same]
  exact SourceCurrentAllocatedConjunctionMemo.advance_self before

/-- The actual current binder graph retains every caller table and the exact cleanup result. -/
theorem kernel_current_binder [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {inherited : SourceEqualityConstraintAllocation.Value}
    {before after : Caller width} {entry : Cache.Interned InternedBinderProtocol.NodeKey}
    {body depth ordinary result : Value Symbol Guard}
    (trace : SourceCurrentAllocatedPartialGraph.NodeBody budget
      ⟨inherited, .mu entry body depth ordinary⟩ before result after)
    (ready : Ready before.checked) (probes : ProbeHeap before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap (.mu entry body depth ordinary)) :
    result = cleanup (.mu entry body depth ordinary) ∧ after = before := by
  cases trace with
  | binder actual =>
      obtain ⟨resultSame, heapSame⟩ := actual_rebuild before.checked ready probes entry body depth ordinary available _ _ actual
      refine ⟨resultSame, ?_⟩
      rw [heapSame]
      cases before with
      | mk checked merge fourth nodes edges =>
          cases checked
          rfl

end MicroCFTA.SourceCurrentAllocatedMuRebuild
