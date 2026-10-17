import MicroCFTA.SourceCurrentAllocatedRawRebuild
import MicroCFTA.SourceCurrentEditFrame

/-!
# Initial resources for raw outer reconstruction

The original field and ordered returned payloads determine reconstruction.
The initial payload count bounds one literal constructor and its stored winner.
Open available inputs need no finite Cap or completed future worker.
-/
namespace MicroCFTA.SourceCurrentRawRebuildNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapTargetForecast (scalar)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
export SourceCurrentEditFrame (constructorProfile constructorProfile_ge constructorProfile_mono constructorProfile_count_mono)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "rawEdge" => SourceCurrentAllocatedRawRebuild.edge
local notation "rawModify" => SourceCurrentAllocatedRawRebuild.modify
variable {width : Nat} [DecidableEq (EdgeKey Symbol Guard)]

private theorem scalar_fits {before : Checked width} (profile : Profile) (fits : Fits profile before) :
    SourceCurrentMemoMergeResourceControl.Fits (scalar profile) before.native.machine.heap :=
  ⟨fits.stored.mono (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile),
    Nat.le_trans fits.nodes (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile),
    Nat.le_trans fits.edges (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile), Nat.zero_le _⟩

/-- Initial physical inputs construct the literal raw equal-arity edge and its full Frame. -/
theorem edge (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (profile : Profile) (fits : Fits profile before)
    (resident : EdgeResident before.native.machine.heap original) (available : Values before.native.machine.heap children)
    (same : children.length = original.children.length) :
    let actual := rawEdge original children before
    SourceCurrentAllocatedRawRebuild.EdgeReceipt formulas solver inventory original children before actual.1 actual.2 ∧
      Frame formulas solver inventory actual.2 ∧ Fits (constructorProfile children.length profile) actual.2 ∧
      actual.2.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      actual.2.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  have receipt := SourceCurrentAllocatedRawRebuild.edge_verified formulas solver inventory original children before
    frame.ready frame.admitted resident available same
  have resources := SourceCurrentMemoMergeResourceControl.edge original.entry.key.symbol original.entry.key.constraint
    children before.native.machine.heap (scalar profile) children.length (scalar_fits profile fits) available (Nat.le_refl _)
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain (rawEdge original children before).2.native.machine.heap :=
    frame.context.guards
  exact ⟨receipt, SourceCurrentConstrainedCapOperandFrame.advance frame receipt.ready receipt.extension
      receipt.nodes receipt.edges guards,
    ⟨resources.1.nodes, resources.1.edges, fits.domains, resources.1.stored⟩, resources.2.2⟩

/-- Both ordered-identity node branches retain the exact old receipt and initial numeric resources. -/
theorem modify (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (entry : Interned InternedBinderProtocol.NodeKey) (oldRows newRows : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (before : Checked width)
    (frame : Frame formulas solver inventory before) (profile : Profile) (fits : Fits profile before)
    (available : Available before.native.machine.heap (.node entry oldRows depth free))
    (resident : Edges before.native.machine.heap newRows) :
    let original := Value.node entry oldRows depth free
    let actual := rawModify original oldRows newRows before
    SourceCurrentAllocatedRawRebuild.NodeReceipt formulas solver inventory original oldRows newRows before actual.1 actual.2 ∧
      Frame formulas solver inventory actual.2 ∧ Fits (constructorProfile newRows.length profile) actual.2 ∧
      actual.2.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + 1 ∧
      actual.2.native.machine.heap.edges.next = before.native.machine.heap.edges.next := by
  have receipt := SourceCurrentAllocatedRawRebuild.modify_verified formulas solver inventory entry oldRows newRows depth free before
    frame.ready frame.admitted available resident
  by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
  · rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same] at receipt ⊢
    exact ⟨receipt, frame, fits.mono (constructorProfile_ge _ _), Nat.le_add_right _ _, rfl⟩
  · have resources := SourceCurrentMemoMergeResourceControl.node newRows before.native.machine.heap
      (scalar profile) newRows.length (scalar_fits profile fits) resident (Nat.le_refl _)
    have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain
        (rawModify (.node entry oldRows depth free) oldRows newRows before).2.native.machine.heap := by
      simp only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte]
      exact SourceCurrentConstrainedCapGuardHeap.preserve Plain _ _ frame.context.guards
        (InternedShallowHeap.makeNode_noNewMu newRows before.native.machine.heap)
    refine ⟨receipt, SourceCurrentConstrainedCapOperandFrame.advance frame receipt.ready receipt.extension
      receipt.nodes receipt.edges guards, ?_, ?_⟩
    · simpa only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte] using
        (show Fits (constructorProfile newRows.length profile)
          (SourceCurrentAllocatedQueryMemo.advancePhysical before
            ⟨(run (makeNode newRows) before.native.machine.heap).2, before.operations⟩) from
          ⟨resources.1.nodes, resources.1.edges, fits.domains, resources.1.stored⟩)
    · simpa only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte] using resources.2.2

end MicroCFTA.SourceCurrentRawRebuildNumeric
