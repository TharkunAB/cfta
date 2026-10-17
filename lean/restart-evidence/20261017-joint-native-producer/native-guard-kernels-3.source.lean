import MicroCFTA.SourceCurrentConstrainedCapNativeGuardHeap
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.NativeGuardIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap

/-- Actual source writes produce the guard heap used by a literal optional-binder prefix. -/
theorem constructed_binder_prefix [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (expression : Syntax Symbol Guard) (pair : Nat × Nat)
    (width : Nat) (operations : SourceEqualityConstraintMemoAllocation.State) :
    ∃ value heap result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap ∧
      let before : State width := ⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace 1
        (.code (.optionalBinder pair (.reference (.intersection pair.1 pair.2)) .pure)) before
        (.code (.pure result)) after ∧
      SourceEqualityRequiredCache.Ready after.native.machine.heap ∧ Guards annotation after.native.machine.heap ∧
      after.operations = operations := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have ready := SourceEqualityRequiredCache.constructed expression value heap built
  have guards : Guards annotation heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentConstrainedCapGuardExecution.closed_heap annotation expression
  let body : Value Symbol Guard := .reference (.intersection pair.1 pair.2)
  have available : Available heap body := reference_available heap _ (by
    intro name member
    simp only [Value.free, List.mem_cons] at member
    rcases member with impossible | absent
    · cases impossible
    · cases absent)
  obtain ⟨result, finalHeap, done, _semantic, _guards, _covered, _resident, _growth, _history⟩ :=
    SourceCurrentConstrainedCapGuardNative.complete annotation pair body heap ready.semantic available ready.covered guards
  let before : State width := ⟨initial width ⟨heap, Cache.emptyState⟩, operations⟩
  let after : State width := ⟨SourceRecursiveIntersectionThunks.advance before.native
    {before.native.machine with heap := finalHeap}, operations⟩
  have one : step (.code (.optionalBinder pair body .pure)) before = .yielded (.code (.pure result)) after := by
    simp only [step, SourceRecursiveIntersectionNative.step]
    change lift operations
      (match SourceRecursiveIntersectionMaybeMu.maybeMu pair body heap with
      | .done value final => SourceRecursiveIntersectionNative.Outcome.yielded (.pure value)
          (SourceRecursiveIntersectionThunks.advance before.native {before.native.machine with heap := final})
      | .pending key final => SourceRecursiveIntersectionNative.Outcome.blocked (.constructor key) (.optionalBinder pair body .pure)
          (SourceRecursiveIntersectionThunks.advance before.native {before.native.machine with heap := final})) = _
    rw [done]
    rfl
  have trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace 1
      (.code (.optionalBinder pair body .pure)) before (.code (.pure result)) after :=
    .cons _ _ _ _ _ _ 0 available one (.refl _ _)
  have retained := SourceCurrentConstrainedCapNativeGuardHeap.trace_heap annotation trace ready guards
  exact ⟨value, heap, result, after, built, trace, retained.1, retained.2, rfl⟩

#print axioms constructed_binder_prefix
#check @constructed_binder_prefix
end MicroCFTA.NativeGuardIntegration
