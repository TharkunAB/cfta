import MicroCFTA.SourceCurrentAllocatedTargetQuery
import MicroCFTA.SourcePruningEnumerationNativeGeneratedTerminalProjectable

/-!
# Projectable heaps from the actual admitted target query

The current caller constructs its actual query receipt and physical trace.
That same pure-return trace supplies every finite physical execution plan.
The complete receipt retains its actual returned state and memo history.
Every finite observed query outcome preserves the current guard support.
-/
namespace MicroCFTA.SourcePruningEnumerationTargetQueryProjectable
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "InputsThrough" => SourceCurrentAllocatedNativePhysicalExecution.InputsThrough
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
  (fun guard : Guard => ∃ classes, SourceCompactGuards.sourceEqualities guard = some classes)
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A pure-return physical trace supplies a plan at every finite execution bound. -/
private theorem trace_all_inputs {count : Nat} {control : Control A}
    {before after : Checked width} {value : A}
    (trace : Trace count control before (.code (.pure value)) after) :
    ∀ fuel, InputsThrough fuel control before := by
  induction count generalizing control before with
  | zero =>
      cases trace
      intro fuel
      cases fuel <;> trivial
  | succ count ih =>
      cases trace with
      | cons control state next reached final result inner inputs one rest =>
          intro fuel
          cases fuel with
          | zero => exact inputs
          | succ fuel =>
              exact ⟨inputs, by simpa only [one] using ih rest fuel⟩

/-- Current admission constructs the full query receipt and support for every finite observation. -/
theorem finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (left right : Node) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (current : Heap before.native.machine.heap)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ (next : Inventory) (value : Node) (after : Checked width) (count : Nat),
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right before value after memos ∧
      Trace count (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        before (.code (.pure value)) after ∧
      Heap after.native.machine.heap ∧
      (∀ fuel, InputsThrough fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before) ∧
      ∀ (fuel : Nat) (observed : SourceEqualityNativeDemand.Outcome width Node),
        SourceEqualityNativeDemand.execute fuel
          (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = observed →
        Heap observed.state.native.machine.heap := by
  obtain ⟨next, value, after, source, roots, receipt⟩ :=
    SourceCurrentAllocatedTargetQuery.finite formulas solver inventory left right before ready admitted
      leftAvailable rightAvailable leftClosed rightClosed ranges memos valid
  have actual := receipt.actual
  cases actual with
  | @run count trace =>
      have plans := trace_all_inputs trace
      have supported := SourcePruningEnumerationNativeGeneratedProjectable.node_query_prefix_projectable
        ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ before after (.code (.pure value)) count
          ready.good current trace
      refine ⟨next, value, after, count, source, roots, receipt, trace, supported, plans, ?_⟩
      intro fuel observed computed
      exact SourcePruningEnumerationNativeGeneratedTerminalProjectable.node_query_outcome_projectable
        ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ before fuel observed ready.good current
          (plans fuel) computed

end MicroCFTA.SourcePruningEnumerationTargetQueryProjectable
