import MicroCFTA.SourceCurrentAllocatedTargetCallerResources
import MicroCFTA.SourceCurrentGeneratedQueryGuardResources

/-!
# Initial guard forecasts for actual target steps

The same recorded physical trace has an instruction bound from its entry
profile. This bound gives an explicit execution ceiling and a finite guard
carrier at the returned heap. An existing step needs no additional Room
or joint Frame premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetQuery
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
variable {width fuel : Nat} {left right value : Value Symbol Guard} {before after : Checked width}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem trace_count (profile : Profile)
    (actual : Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before
      (.code (.pure value)) after)
    (ready : Ready before) (fits : Fits profile before)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    fuel ≤ instructionBound profile.nodes profile.edges profile.mass := by
  let source := before.native.machine.heap
  let holds : Guard → Language.Term Symbol → Bool := fun _ _ => true
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have facts := ready.good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source
    facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source
    facts.coherent rightAvailable rightClosed
  have complete := SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have requestReady : NodeReady before.native.machine request :=
    ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have count := SourceCurrentAllocatedNativeInstructionTrace.node_prefix source facts holds request scope complete
    actual ready.good requestReady (grows_refl _) (extends_refl _)
  have initialCount := SourceCurrentAllocatedNativeComputedBudget.nodeBudget_le source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed fits.stored
  have larger := SourceCurrentAllocatedNativeComputedBudget.instructionBound_mono
    fits.nodes fits.edges (Nat.le_refl profile.mass)
  exact Nat.le_trans (Nat.le_trans count initialCount) larger

/-- An actual target step returns at the explicit instruction ceiling of its initial profile. -/
theorem Step.done_profile (profile : Profile) (actual : Step left right before value after)
    (ready : Ready before) (fits : Fits profile before)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    execute (instructionBound profile.nodes profile.edges profile.mass + 1)
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after := by
  cases actual with
  | @run count trace =>
      have bounded := trace_count profile trace ready fits leftAvailable rightAvailable leftClosed rightClosed
      have done := trace_done count _ before after value trace.steps
      have stable := done_stable (count + 1)
        (instructionBound profile.nodes profile.edges profile.mass - count) _ before after value done
      have same : count + 1 + (instructionBound profile.nodes profile.edges profile.mass - count) =
          instructionBound profile.nodes profile.edges profile.mass + 1 := by omega
      rw [same] at stable
      exact stable

/-- The same target step bounds every returned guard by the original alphabet and profile. -/
theorem Step.guard_forecast (alphabet : List Guard) (profile : Profile)
    (actual : Step left right before value after)
    (ready : Ready before) (fits : Fits profile before)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    Heap (fun guard => guard ∈ SourceCurrentGeneratedQueryGuardResources.forecast alphabet profile)
      after.native.machine.heap := by
  cases actual with
  | run trace =>
      have count := trace_count profile trace ready fits leftAvailable rightAvailable leftClosed rightClosed
      exact (SourceCurrentNativeGuardTrace.bounded alphabet
        (instructionBound profile.nodes profile.edges profile.mass) trace ready.good
        (fun _ => trivial) known (fun _ => trivial) count).1

end MicroCFTA.SourceCurrentAllocatedTargetQuery
