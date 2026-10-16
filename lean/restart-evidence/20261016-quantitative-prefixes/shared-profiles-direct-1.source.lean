import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetProfiles
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedForceResources

/-!
# Quantitative profiles of actual shared receipts

A miss proves the actual target profile before the literal store.
A hit reads the existing profile and retains the complete shared state.
The leaf query joins that target profile with its original current input.
No capacity, future profile, or completed enclosing call is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfileProducer
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "targetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next : Inventory}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : State width} {input value result : Value Symbol Guard} {memos final : Memos}

/-- The same actual force derives its fixed target envelope and retains all certificate tables. -/
theorem force_receipt
    {receiptBase : InternedConstructorTemplates.State Symbol Guard}
    (receipt : ForceReceipt formulas solver next record values receiptBase path before value after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat)
    (stored : Stored (targetRows record rows count depth bound) (max arity 1) bound before)
    (profile : ChildrenShape rows arity values) (lengthBound : values.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (heightBound : childrenHeight values ≤ bound) :
    Stored (targetRows record rows count depth bound) (max arity 1) bound after ∧
      NodeShape (targetRows record rows count depth bound) (max arity 1) value ∧ height value ≤ bound := by
  cases receipt.reads with
  | hit present => exact ⟨stored, stored.slots path value present⟩
  | miss absent reads =>
      have available : Values before.checked.native.machine.heap values :=
        fun value member => ready.captured.available value (known value member)
      obtain ⟨merged, native, output, shaped, bounded⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryTargetProfiles.target_reads reads ready.checked available ready.stored
          stored.merge stored.native stored.output rows arity count depth bound profile lengthBound
          (SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds.operand_paths_depth record.paths path depth pathsBound) heightBound
      have operandCount := SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds.record_operand_paths_length record coherent path member
      have produced : NodeShape (targetRows record rows count depth bound) (max arity 1) value := by
        simpa only [targetRows, operandCount] using shaped
      exact ⟨SourceCurrentAllocatedFiniteOrdinarySharedProfiles.store_stored before path value _ _ stored
        native output merged produced bounded, produced, bounded⟩

/-- The same actual leaf derives its current-input height bound and native output envelope. -/
theorem leaf_receipt
    (receipt : LeafReceipt formulas solver next record values base path input before result after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat)
    (stored : Stored (targetRows record rows count depth bound) (max arity 1) bound before)
    (profile : ChildrenShape rows arity values) (lengthBound : values.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (heightBound : childrenHeight values ≤ bound)
    (inputRows inputArity inputBound : Nat) (inputProfile : NodeShape inputRows inputArity input)
    (inputHeight : height input ≤ inputBound) :
    Stored (targetRows record rows count depth bound) (max arity 1) bound after ∧
      NodeShape (max (targetRows record rows count depth bound) inputRows *
        max (targetRows record rows count depth bound) inputRows) (max (max (max arity 1) inputArity) 1) result ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result ∧ height result ≤ inputBound := by
  cases receipt.reads with
  | apply first query =>
      obtain ⟨middleStored, targetProfile, _targetHeight⟩ := force_receipt first ready known coherent member
        rows arity count depth bound stored profile lengthBound pathsBound heightBound
      cases query.actual with
      | run trace =>
          have structural := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace first.ready.checked.good first.ready.checked.semantic
            middleStored.native ⟨rfl, NodeShape.domain _ targetProfile, NodeShape.domain _ inputProfile⟩
          have shaped := SourceCurrentAllocatedFiniteOrdinaryOutputExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace first.ready.checked.good first.ready.checked.semantic
            middleStored.output rfl (max (targetRows record rows count depth bound) inputRows) (max (max arity 1) inputArity)
            (NodeShape.mono _ targetProfile (Nat.le_max_left _ _) (Nat.le_max_left _ _))
            (NodeShape.mono _ inputProfile (Nat.le_max_right _ _) (Nat.le_max_right _ _))
          exact ⟨SourceCurrentAllocatedFiniteOrdinarySharedProfiles.advance_stored _ _ middleStored structural.1 shaped.1,
            shaped.2, ⟨structural.2.1, structural.2.2.2⟩, Nat.le_trans structural.2.2.2 inputHeight⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfileProducer
