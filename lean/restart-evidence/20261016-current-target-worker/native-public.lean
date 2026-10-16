import MicroCFTA.SourceCurrentAllocatedTargetWorkerNative

#print axioms MicroCFTA.SourceCurrentAllocatedTargetWorkerNative.of_done
#print axioms MicroCFTA.SourceCurrentAllocatedTargetWorkerNative.of_done_ready
#print axioms MicroCFTA.SourceCurrentAllocatedTargetWorkerNative.step_iff_done
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetWorkerNative.of_done
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetWorkerNative.of_done_ready
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetWorkerNative.step_iff_done

namespace MicroCFTA.AllocatedTargetWorkerNativeChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedTargetQuery
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Ranges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- The arbitrary native return supplies the trace used for same-return language and memo receipts.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : Ranges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before)
    (done : execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next : Inventory,
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      Receipt formulas solver next left right before value after memos := by
  have actual := SourceCurrentAllocatedTargetWorkerNative.of_done_ready fuel left right before value after
    ready leftAvailable rightAvailable leftClosed rightClosed ranges done
  exact actual.verified formulas solver inventory ready admitted leftAvailable rightAvailable
    leftClosed rightClosed ranges memos valid

-- A larger successful bound retains the exact native tables and equality operations.
example (fuel extra : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : Ranges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before)
    (done : execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after) :
    execute (fuel + extra) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after ∧
      Step left right before value after := by
  have stable := done_stable fuel extra _ before after value done
  exact ⟨stable, SourceCurrentAllocatedTargetWorkerNative.of_done (fuel + extra) left right before value after
    good idle leftAvailable rightAvailable leftClosed rightClosed ranges stable⟩

-- Duplicate empty operands need neither an original-syntax premise nor an input inventory.
example (fuel : Nat) (before after : Checked width) (value : Value Symbol Guard)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (idle : SourceRecursiveIntersectionNative.Idle before.native)
    (ranges : Ranges (.code (requestNode IntersectionEmptyDomain.emptyDomain (.empty : Value Symbol Guard) .empty)) before)
    (done : execute fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain (.empty : Value Symbol Guard) .empty)) before =
      .done value after) : Step .empty .empty before value after :=
  SourceCurrentAllocatedTargetWorkerNative.of_done fuel .empty .empty before value after good idle
    (empty_available _) (empty_available _) rfl rfl ranges done

-- Exhaustion remains a yielded observation. The bridge does not make zero fuel succeed.
example (left right : Value Symbol Guard) (before : Checked width) :
    execute 0 (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before =
      .yielded (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before := rfl

end MicroCFTA.AllocatedTargetWorkerNativeChecks
