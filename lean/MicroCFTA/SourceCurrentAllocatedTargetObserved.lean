import MicroCFTA.SourceCurrentAllocatedTargetQuery
import MicroCFTA.SourceCurrentAllocatedNativeObservedWords

namespace MicroCFTA.SourceCurrentAllocatedTargetQuery
open InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual recorded target step supplies its own numeric prefix checks. -/
theorem Step.wordRanges {left right value : Value Symbol Guard} {before after : Checked width}
    (actual : Step left right before value after) :
    SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before := by
  cases actual with
  | run trace => exact SourceCurrentAllocatedNativeObservedWords.trace_wordRanges trace

/-- A recorded target step derives its receipts without a separate range premise.
The step already contains each actual instruction's physical input checks. -/
theorem Step.verified_observed
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {left right value : Value Symbol Guard} {before after : Checked width}
    (actual : Step left right before value after)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ next : Inventory,
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      Receipt formulas solver next left right before value after memos :=
  actual.verified formulas solver inventory ready admitted leftAvailable rightAvailable leftClosed rightClosed
    actual.wordRanges memos valid

end MicroCFTA.SourceCurrentAllocatedTargetQuery
