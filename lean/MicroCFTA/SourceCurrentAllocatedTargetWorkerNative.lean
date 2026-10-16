import MicroCFTA.SourceCurrentAllocatedTargetQuery

/-!
# Checked native returns for current target workers

A completed native execution does not by itself provide physical input
checks. Initial physical validity, idle cells, closed resident operands,
and reached word ranges construct a physical trace independently.
Successful execution uniqueness identifies its full returned state with
the supplied native return. No input model or global memo law is needed
for this physical bridge.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetWorkerNative
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedTargetQuery (Step)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
variable {width : Nat}

/-- Initial physical checks derive a trace at the supplied completed native return. -/
theorem of_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width)
    (good : Good before) (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before)
    (done : execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before =
      .done value after) : Step left right before value after := by
  have facts := good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original
    left before.native.machine.heap facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original
    right before.native.machine.heap facts.coherent rightAvailable rightClosed
  obtain ⟨count, result, final, receipt, _⟩ :=
    SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete (fun _ _ => true)
      before good idle left right leftOriginal rightOriginal leftAvailable rightAvailable
      leftClosed rightClosed ranges
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique
    fuel (count + 1) _ before after final value result done receipt.done
  exact .run receipt.trace

/-- Current target readiness supplies the physical checks at its actual native entry. -/
theorem of_done_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before)
    (done : execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before =
      .done value after) : Step left right before value after :=
  of_done fuel left right before value after ready.good ready.idle
    leftAvailable rightAvailable leftClosed rightClosed ranges done

/-- On this initial physical domain, a raw step is exactly some completed native execution. -/
theorem step_iff_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width)
    (good : Good before) (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before) :
    Step left right before value after ↔
      ∃ fuel, execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before =
        .done value after := by
  constructor
  · exact Step.done
  · rintro ⟨fuel, done⟩
    exact of_done fuel left right before value after good idle leftAvailable rightAvailable
      leftClosed rightClosed ranges done

end MicroCFTA.SourceCurrentAllocatedTargetWorkerNative
