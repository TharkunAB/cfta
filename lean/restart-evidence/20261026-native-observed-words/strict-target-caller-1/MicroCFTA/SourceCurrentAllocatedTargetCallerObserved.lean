import MicroCFTA.SourceCurrentAllocatedTargetObserved
import MicroCFTA.SourceCurrentAllocatedTargetInitial
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

namespace MicroCFTA.SourceCurrentAllocatedTargetQuery
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq (EdgeKey Symbol Guard)]
variable {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
  {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next : Inventory}
  {before : Caller width} {after : Checked width} {left right value : Value Symbol Guard} {memos : Memos}

/-- An actual query receipt preserves the full outer caller at its literal returned checked state. -/
theorem receipt_post [DecidableEq Symbol]
    (initial : Context formulas solver inventory before memos)
    (receipt : Receipt formulas solver next left right before.checked value after memos) :
    Post formulas solver next before
      (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) memos := by
  have probes : InternedFreshOrdinaryProbeHeap.Heap after.native.machine.heap := by
    cases receipt.actual with
    | run trace => exact SourceCurrentAllocatedMuRebuild.trace_heap trace initial.ready.semantic initial.probes
  exact ⟨⟨receipt.ready, receipt.admitted,
    initial.sound.advance formulas solver after before.fourth before.merge receipt.effects,
    initial.stored.grows receipt.effects.keeps, initial.covered,
    SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps before.fourth initial.correct,
    receipt.globals, probes⟩, receipt.effects, Cache.extends_refl _, fun _ _ found => found⟩

/-- Initial numeric room verifies the exact raw query return and its full outer postcondition. -/
theorem raw_done_caller_initial [DecidableEq Symbol] (bits fuel : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller (bits + 2)) (after : Checked (bits + 2))
    (left right value : Value Symbol Guard) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (leftAvailable : Available before.checked.native.machine.heap left)
    (rightAvailable : Available before.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : before.checked.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.checked.native.machine.domains.next +
      2 ^ (before.checked.native.machine.heap.nodes.next +
        before.checked.native.machine.heap.nodes.next * before.checked.native.machine.heap.nodes.next) < 2 ^ (bits + 1))
    (done : SourceEqualityNativeDemand.execute fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      before.checked = .done value after) :
    ∃ next : Inventory,
      next.source = before.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      Receipt formulas solver next left right before.checked value after memos ∧
      Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) memos := by
  obtain ⟨next, source, roots, receipt⟩ := raw_done_verified_initial bits fuel formulas solver inventory
    left right value before.checked after initial.ready initial.admitted leftAvailable rightAvailable
    leftClosed rightClosed nodes edges room memos initial.globals done
  exact ⟨next, source, roots, receipt, receipt_post initial receipt⟩

end MicroCFTA.SourceCurrentAllocatedTargetQuery
