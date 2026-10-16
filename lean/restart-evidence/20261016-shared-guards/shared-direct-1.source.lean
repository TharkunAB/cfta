import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardIteration
import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf

/-!
# Causal hereditary guard bounds in shared target slots

Each slot refers to the captured original forest and its literal target paths.
A miss derives the universal slot law from the same actual target reads.
A hit uses the stored law without changing the checked state or merge memo.
A leaf joins that target bound with its original current input bound.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardShared
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State initial advance store)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Node" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "Children" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "targetLimit" => SourceCurrentAllocatedFiniteOrdinaryGuardTarget.targetLimit
local notation "leafLimit" => SourceCurrentAllocatedFiniteOrdinaryGuardIteration.leafLimit
variable {width : Nat}

/-- A slot retains the law for its captured original forest and literal operand path order. -/
def Certificate (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (value : Value Symbol Guard) : Prop :=
  ∀ limits, Children limits values →
    Node (targetLimit limits (SourceEqualityClassTarget.operandPaths record.paths path)) value

/-- Native, merge, and shared-slot tables retain their separate causal guard laws. -/
structure Stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) : Prop where
  native : NativeStored state.checked.native
  merge : MergeStored state.memo
  slots : ∀ path value, state.targets path = some value → Certificate record values path value

/-- Class initialization clears only slots and retains both warm certificate tables. -/
theorem initial_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (checked : Checked width) (memo : Memo) (native : NativeStored checked.native) (merged : MergeStored memo) :
    Stored record values (initial checked memo) :=
  ⟨native, merged, by intro path value absent; cases absent⟩

/-- Actual checked advancement retains the captured forest and every slot law. -/
theorem advance_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) (checked : Checked width) (stored : Stored record values state)
    (native : NativeStored checked.native) : Stored record values (advance state checked) :=
  ⟨native, stored.merge, stored.slots⟩

/-- Constructor advancement changes no native returned cells, slots, or merge entries. -/
theorem advance_heap_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) (heap : InternedConstructorTemplates.State Symbol Guard)
    (stored : Stored record values state) :
    Stored record values (advance state
      (SourceCurrentAllocatedQueryMemo.advancePhysical state.checked ⟨heap, state.checked.operations⟩)) :=
  advance_stored record values state _ stored
    (SourceCurrentAllocatedFiniteOrdinaryGuardStored.advance_stored _ _ stored.native)

/-- A derived target law enters its actual slot while all earlier slot laws remain valid. -/
theorem store_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (checked : Checked width) (memo : Memo) (stored : Stored record values state)
    (native : NativeStored checked.native) (merged : MergeStored memo)
    (certificate : Certificate record values path value) :
    Stored record values (store state path value checked memo) := by
  refine ⟨native, merged, ?_⟩
  intro other result found
  by_cases same : other = path
  · subst other
    have resultSame : value = result := Option.some.inj (by simpa only [store, put, ite_true] using found)
    exact resultSame ▸ certificate
  · exact stored.slots other result (by simpa only [store, put, same, ite_false] using found)

section Producers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next : Inventory}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : State width} {input value result : Value Symbol Guard} {memos final : Memos}

/-- The same actual force derives its slot law before store and retains all three tables. -/
theorem force_receipt
    (receipt : ForceReceipt formulas solver next record values base path before value after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (stored : Stored record values before) (limits : Limits) (profile : Children limits values) :
    Stored record values after ∧
      Node (targetLimit limits (SourceEqualityClassTarget.operandPaths record.paths path)) value := by
  cases receipt.reads with
  | hit present => exact ⟨stored, stored.slots path value present limits profile⟩
  | miss absent reads =>
      have available : Values before.checked.native.machine.heap values :=
        fun value member => ready.captured.available value (known value member)
      have own := SourceCurrentAllocatedFiniteOrdinaryGuardTarget.target_reads reads ready.checked
        available ready.stored stored.merge stored.native limits profile
      have certificate : Certificate record values path value := by
        intro other otherProfile
        exact (SourceCurrentAllocatedFiniteOrdinaryGuardTarget.target_reads reads ready.checked
          available ready.stored stored.merge stored.native other otherProfile).2.2
      exact ⟨store_stored record values before path value _ _ stored own.2.1 own.1 certificate, own.2.2⟩

/-- The actual leaf query uses the forced target and current input at their common envelope. -/
theorem leaf_receipt
    (receipt : LeafReceipt formulas solver next record values base path input before result after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (stored : Stored record values before) (captured inputLimits : Limits)
    (profile : Children captured values) (inputProfile : Node inputLimits input) :
    Stored record values after ∧ Node (leafLimit record captured inputLimits) result := by
  cases receipt.reads with
  | apply first query =>
      have forced := force_receipt first ready known stored captured profile
      cases query.actual with
      | run trace =>
          have checked := SourceCurrentAllocatedFiniteOrdinaryGuardExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace
            first.ready.checked.good first.ready.checked.semantic forced.1.native rfl
            (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.join
              (SourceCurrentAllocatedFiniteOrdinaryGuardTarget.foldLimit captured record.paths.length) inputLimits)
            (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.mono _ forced.2
              (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_trans
                (SourceCurrentAllocatedFiniteOrdinaryGuardIteration.target_le_record record path captured)
                (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_join_left _ _)))
            (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.mono _ inputProfile
              (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_join_right _ _))
          exact ⟨advance_stored record values _ _ forced.1 checked.1, checked.2⟩

end Producers
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardShared
