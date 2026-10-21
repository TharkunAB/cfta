import MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion
import MicroCFTA.SourceCurrentAllocatedTargetQuery

/-!
# Scope of the same completed checked native request

A completed physical trace supplies its own checked request word ranges.
The existing scope completion then aligns with the same actual return.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeActualScope
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Words" => SourceCurrentAllocatedNativeRequestBounds.Words
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {A : Type} {width fuel : Nat}

private theorem inputs_words (control : Control A) (before : Checked width)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before) : Words width control := by
  cases control with
  | edgeBody => trivial
  | code code =>
      cases code with
      | node | edge => exact inputs.2
      | pure | fail | work | enter | read | optionalBinder | finishNode | finishEdge => trivial

/-- A completed physical trace supplies all checked-prefix request word checks. -/
theorem word_ranges {control : Control A} {before after : Checked width} {value : A}
    (actual : Trace fuel control before (.code (.pure value)) after) : WordRanges control before := by
  induction fuel generalizing control before with
  | zero =>
      cases actual
      intro count next current prefixTrace
      cases prefixTrace with
      | refl => trivial
      | cons _ _ _ _ _ _ _ one _ =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
  | succ fuel ih =>
      cases actual with
      | cons control before next current _ _ _ inputs one rest =>
          intro count final reached prefixTrace
          cases prefixTrace with
          | refl => exact inputs_words control before inputs
          | cons _ _ other middle _ _ _ observed tail =>
              obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (one.symm.trans observed)
              exact ih rest _ _ _ tail

/-- The same actual closed request returns scoped cells, an idle cache, and a closed value. -/
theorem step {left right result : Value Symbol Guard} {before after : Checked width}
    (actual : SourceCurrentAllocatedTargetQuery.Step left right before result after)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped before.native)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ result.free = [] := by
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left before.native.machine.heap
    good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right before.native.machine.heap
    good.native.machine.1.coherent rightAvailable rightClosed
  have ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before := by
    cases actual with
    | run trace => exact word_ranges trace
  obtain ⟨count, value, reached, receipt, returnedIdle, closed⟩ :=
    SourceCurrentAllocatedNativeScopeCompletion.initial_complete (fun _ _ => true) before good scopedCache semantic idle
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  obtain ⟨rfl, rfl⟩ := actual.unique (.run receipt.trace)
  exact ⟨receipt.scopedCache, returnedIdle, closed⟩

end MicroCFTA.SourceCurrentAllocatedNativeActualScope

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentAllocatedNativeActualScope.word_ranges
#print MicroCFTA.SourceCurrentAllocatedNativeActualScope.word_ranges
#print axioms MicroCFTA.SourceCurrentAllocatedNativeActualScope.word_ranges
#check @MicroCFTA.SourceCurrentAllocatedNativeActualScope.step
#print MicroCFTA.SourceCurrentAllocatedNativeActualScope.step
#print axioms MicroCFTA.SourceCurrentAllocatedNativeActualScope.step
