import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
import MicroCFTA.SourceCurrentConstrainedCapMixedTarget

/-!
# Generated-query invariants through selected Operand work

The actual projection and Merge retain the same native cells and inventory.
Their produced guard heap retains the complete query frame at the literal
returned state. Selected closure permits unrelated open ordinary roots.
These results do not derive a numeric resource forecast for Operand work.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapOperandFrame
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedTargetGraph (Operand)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
variable {width : Nat}

/-- A full query frame derives both joint stores at the literal current heap. -/
theorem current {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory} {state : Checked width}
    (frame : Frame formulas solver inventory state) : SourceCurrentConstrainedCapCurrentNative.At Plain state :=
  SourceCurrentConstrainedCapCurrentNative.rebase Plain inventory.source state inventory.facts frame.ready.good
    frame.context frame.joint frame.origins

/-- Actual heap growth and unchanged native cells retain every part of the same query frame. -/
theorem advance {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory} {before after : Checked width}
    (frame : Frame formulas solver inventory before) (ready : Ready after)
    (extension : Extension before.native.machine after.native.machine)
    (nodes : after.native.nodes = before.native.nodes) (edges : after.native.edges = before.native.edges)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain after.native.machine.heap) :
    Frame formulas solver inventory after := by
  refine ⟨ready, ?_, frame.context.after ready.good.native.machine ready.semantic.ready.semantic guards extension,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ⟨⟨by simpa only [nodes] using frame.admitted.contextual.nodes,
      by simpa only [edges] using frame.admitted.contextual.edges⟩,
      ⟨by simpa only [nodes] using frame.admitted.covered.nodes,
        by simpa only [edges] using frame.admitted.covered.edges⟩,
      grows_trans frame.admitted.growth extension.heap, extends_trans frame.admitted.history extension.history⟩
  · simpa only [nodes] using frame.joint.nodes
  · simpa only [edges] using frame.joint.edges
  · simpa only [nodes] using frame.origins.nodes
  · simpa only [edges] using frame.origins.edges

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual selected Operand retains the full query frame without an all-root cap premise. -/
theorem of_receipt {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
    {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo result after saved memos final)
    (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) : Frame formulas solver inventory after := by
  obtain ⟨projected, middle, currentMemos, projection, merged⟩ := receipt.actual
  have projectedGuards := SourceCurrentConstrainedCapProjectionGuard.forest Plain projection.graph
    frame.ready.semantic frame.ready.costs available frame.context.guards
  have returnedGuards : SourceCurrentConstrainedCapGuardHeap.Heap Plain after.native.machine.heap := by
    cases merged.actual with
    | done actual =>
        exact SourceCurrentConstrainedCapMergeJointEffects.call_heap Plain actual.graph
          projection.ready.semantic projection.ready.costs (physicalStored.grows projection.effects.keeps)
          projection.available projectedGuards
  have extension : Extension before.native.machine after.native.machine :=
    ⟨receipt.effects.keeps.growth, receipt.effects.keeps.history, by
      simpa only [receipt.domains] using extends_refl before.native.machine.domains.table⟩
  exact advance frame receipt.ready extension receipt.nodes receipt.edges returnedGuards

/-- Initial selected support constructs an Operand and its full returned query frame. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : Domain path values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ result after saved final,
      Operand path values before memo result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
        before memo result after saved memos final ∧ Frame formulas solver inventory after := by
  obtain ⟨result, after, saved, final, actual, receipt⟩ := Operand.complete formulas solver inventory path values
    before memo frame.ready frame.admitted available domain physicalStored covered memos valid
  exact ⟨result, after, saved, final, actual, receipt, of_receipt receipt frame available physicalStored⟩

/-- The same constructed Operand also derives its selected cap and retains the populated Merge laws. -/
theorem mixed_complete (depth : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : Domain path values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (merged : MergeStored memo) (bounded : ∀ value ∈ values, SourceCurrentConstrainedCap.Cap Plain depth value) :
    ∃ result after saved final,
      Operand path values before memo result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
        before memo result after saved memos final ∧ Frame formulas solver inventory after ∧
      MergeStored saved ∧ SourceCurrentConstrainedCap.Cap Plain
        (SourceCurrentConstrainedCapMixedTarget.operandDepth depth path) result := by
  obtain ⟨result, after, saved, final, actual, receipt, returned⟩ :=
    complete formulas solver inventory path values before memo frame available domain physicalStored covered memos valid
  have capped := SourceCurrentConstrainedCapMixedTarget.operand_receipt depth receipt frame.ready available domain
    physicalStored merged (current frame) bounded
  exact ⟨result, after, saved, final, actual, receipt, returned, capped.1, capped.2.2⟩

end MicroCFTA.SourceCurrentConstrainedCapOperandFrame
