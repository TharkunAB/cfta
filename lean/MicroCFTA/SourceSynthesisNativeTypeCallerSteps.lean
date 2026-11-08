import MicroCFTA.SourceCurrentAllocatedPartialStepEffects
import MicroCFTA.SourceSynthesisNativeTypeSharedState
import MicroCFTA.SourceSynthesisNativeTypeSharedHeap
import MicroCFTA.SourceSynthesisHereditaryMemoFields

/-!
# Type facts through actual inherited and constructor caller steps

Inherited combination and indexed descent change equality operations.
The native state, warm Merge memo, and both outer result families stay
unchanged. Each actual operation derives its returned physical readiness
and full caller postcondition. The same return retains Type readiness,
the conditional guard profile, and hereditary memo history.

Raw reconstruction retains the same warm owners and result histories.
These laws concern finite caller steps. They do not prove
recursive completion, all reached classifications, or a global bound.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeCallerSteps
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceSynthesisHereditaryMemoFields (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable {width : Nat}

private theorem operations_ready (lib : Library) (before : Caller width)
    (ready : Ready lib (initial before.checked before.merge)) (checked : Checked width)
    (same : checked.native = before.checked.native)
    (physical : SourceCurrentConjunctionClassScan.Ready checked) :
    Ready lib (initial checked before.merge) := by
  have next : SourceSynthesisNativeTypeClosedRequests.Ready lib checked :=
    ⟨physical.good, physical.semantic,
      by simpa only [SourceCurrentAllocatedSharedTargetState.initial, same] using ready.checked.scopes,
      by simpa only [SourceCurrentAllocatedSharedTargetState.initial, same] using ready.checked.idle,
      ⟨by simpa only [SourceCurrentAllocatedSharedTargetState.initial, same] using ready.checked.stored.constructors,
        by simpa only [SourceCurrentAllocatedSharedTargetState.initial, same] using ready.checked.stored.native⟩⟩
  exact SourceSynthesisNativeTypeSharedState.initial lib checked before.merge next
    (by simpa only [SourceCurrentAllocatedSharedTargetState.initial, same] using ready.costs)
    (by simpa only [SourceCurrentAllocatedSharedTargetState.initial, same] using ready.physicalMemo) ready.typedMemo

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The literal inherited prefix retains the same caller and Type histories at its returned operations. -/
theorem inherited_prefix (lib : Library) (literal : String → Symbol)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (ready : Ready lib (initial before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (history : History lib literal before)
    (edge : EdgeValue Symbol Guard) (inherited : EqValue)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited) :
    ∃ payload, SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory edge.entry.key.constraint inherited before.checked payload ∧
      Post formulas solver inventory before (prefixState before edge inherited) memos ∧
      Ready lib (initial (prefixState before edge inherited).checked (prefixState before edge inherited).merge) ∧
      GuardHeap (Origin lib) (prefixState before edge inherited).checked.native.machine.heap ∧
      History lib literal (prefixState before edge inherited) := by
  obtain ⟨payload, prefixReceipt⟩ := SourceCurrentAllocatedInheritedPrefix.resident_finite formulas solver inventory
    edge inherited before.checked context.ready context.admitted resident inheritedReady
  obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix formulas solver inventory before memos
    context edge inherited payload resident inheritedReady prefixReceipt.actual
  refine ⟨payload, receipt, post, ?_, guards, ?_⟩
  · exact operations_ready lib before ready (prefixState before edge inherited).checked rfl receipt.ready
  · exact SourceSynthesisHereditaryMemoFields.advance history _ _ _

/-- Actual indexed descent derives the child payload and retains Type readiness and both memo histories. -/
theorem descent (lib : Library) (literal : String → Symbol)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (ready : Ready lib (initial before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (history : History lib literal before) (combined : EqValue) (index : Nat)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints combined) :
    SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory before combined index ∧
      Post formulas solver inventory before (descend before combined index).2 memos ∧
      Ready lib (initial (descend before combined index).2.checked (descend before combined index).2.merge) ∧
      GuardHeap (Origin lib) (descend before combined index).2.checked.native.machine.heap ∧
      History lib literal (descend before combined index).2 := by
  obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver inventory before memos
    context combined index inheritedReady
  refine ⟨receipt, post, ?_, guards, ?_⟩
  · exact operations_ready lib before ready (descend before combined index).2.checked
      (SourceCurrentAllocatedPartialDescent.components before combined index).2.1 receipt.ready
  · exact SourceSynthesisHereditaryMemoFields.advance history _ _ _

/-- Actual equal-arity raw edge work retains Type readiness and the complete earlier caller histories. -/
theorem raw_edge (lib : Library) (literal : String → Symbol)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (ready : Ready lib (initial before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (history : History lib literal before) (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard))
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap original)
    (available : Values before.checked.native.machine.heap children) (same : children.length = original.children.length) :
    let returned := SourceCurrentAllocatedRawRebuild.edge original children before.checked
    let after := SourceCurrentAllocatedPartialState.advance before returned.2 before.fourth before.merge
    SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver inventory original children before.checked returned.1 returned.2 ∧
      Post formulas solver inventory before after memos ∧ Ready lib (initial after.checked after.merge) ∧
      GuardHeap (Origin lib) after.checked.native.machine.heap ∧ History lib literal after := by
  obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.raw_edge formulas solver inventory before memos
    context original children resident available same
  have typed := SourceSynthesisNativeTypeSharedHeap.edge lib original children rfl ready resident available
  exact ⟨receipt, post, typed.1, guards, SourceSynthesisHereditaryMemoFields.advance history _ _ _⟩

/-- Both actual modifyNode branches retain Type readiness and the complete earlier caller histories. -/
theorem raw_modify (lib : Library) (literal : String → Symbol)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (ready : Ready lib (initial before.checked before.merge))
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap)
    (history : History lib literal before)
    (entry : Interned InternedBinderProtocol.NodeKey) (oldRows newRows : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available before.checked.native.machine.heap (.node entry oldRows depth free))
    (resident : Edges before.checked.native.machine.heap newRows) (closed : ClosedEdges newRows) :
    let original := Value.node entry oldRows depth free
    let returned := SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before.checked
    let after := SourceCurrentAllocatedPartialState.advance before returned.2 before.fourth before.merge
    SourceCurrentAllocatedRawRebuild.NodeReceipt formulas solver inventory original oldRows newRows
        before.checked returned.1 returned.2 ∧
      Post formulas solver inventory before after memos ∧ Ready lib (initial after.checked after.merge) ∧
      GuardHeap (Origin lib) after.checked.native.machine.heap ∧ History lib literal after := by
  obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.modify formulas solver inventory before memos
    context entry oldRows newRows depth free available resident
  have retained : Ready lib (initial
        (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).2 before.merge) ∧
      GuardHeap (Origin lib)
        (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).2.native.machine.heap := by
    by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
    · rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same]
      exact ⟨ready, guards⟩
    · have actual : SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked =
          ((run (makeNode newRows) before.checked.native.machine.heap).1,
            SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
              ⟨(run (makeNode newRows) before.checked.native.machine.heap).2, before.checked.operations⟩) := by
        simp only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte]
        rfl
      rw [actual]
      have typed := SourceSynthesisNativeTypeSharedHeap.node lib rfl ready resident closed
      exact ⟨typed.1, SourceCurrentConstrainedCapGuardHeap.preserve (Origin lib) _ _ guards
        (InternedShallowHeap.makeNode_noNewMu newRows before.checked.native.machine.heap)⟩
  exact ⟨receipt, post, retained.1, retained.2, SourceSynthesisHereditaryMemoFields.advance history _ _ _⟩

end MicroCFTA.SourceSynthesisNativeTypeCallerSteps
