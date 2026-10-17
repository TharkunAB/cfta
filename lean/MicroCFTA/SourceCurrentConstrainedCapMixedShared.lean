import MicroCFTA.SourceCurrentConstrainedCapMixedTarget
import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf

/-!
# Finite-depth shared targets and actual leaf queries

A slot certificate uses the immutable class forest and the exact other-path
operand list. A miss derives that certificate before storage. A leaf query
uses the maximum cap depth of its produced target and current input.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMixedShared
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State initial advance store Ready)
open SourceCurrentAllocatedSharedTargetForce (Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "operands" => SourceEqualityClassTarget.operandPaths
local notation "targetDepth" => SourceCurrentConstrainedCapMixedTarget.targetDepth
variable {width : Nat}

/-- Every depth law uses the original captured forest and its selected path domains. -/
def Certificate (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (value : Value Symbol Guard) : Prop :=
  ∀ depth, (∀ original ∈ values, Cap Plain depth original) →
    (∀ operand ∈ operands record.paths path, Domain operand values) →
    Cap Plain (targetDepth depth (operands record.paths path)) value

/-- Current native laws and universal Merge and slot laws follow the actual shared state. -/
structure Stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) : Prop where
  /-- The literal current heap interprets both native tables and their captured origins. -/
  current : Current state.checked
  /-- Each Merge result retains every depth of its complete captured original. -/
  merge : MergeStored state.memo
  /-- Every present slot retains the law of its immutable captured class forest. -/
  slots : ∀ path value, state.targets path = some value → Certificate record values path value

/-- Fresh slots retain the supplied warm native and Merge tables. -/
theorem initial_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (checked : Checked width) (memo : Memo) (current : Current checked) (merged : MergeStored memo) :
    Stored record values (initial checked memo) :=
  ⟨current, merged, by intro path value absent; cases absent⟩

/-- An actual checked return retains the same slot certificates and Merge table. -/
theorem advance_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) (checked : Checked width) (stored : Stored record values state) (current : Current checked) :
    Stored record values (advance state checked) := ⟨current, stored.merge, stored.slots⟩

/-- A newly stored target carries the certificate derived for that same actual result. -/
theorem store_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (checked : Checked width) (memo : Memo) (stored : Stored record values state)
    (current : Current checked) (merged : MergeStored memo) (certificate : Certificate record values path value) :
    Stored record values (store state path value checked memo) := by
  refine ⟨current, merged, ?_⟩
  intro other result found
  by_cases same : other = path
  · subst other
    have sameResult : value = result := Option.some.inj (by simpa only [store, put, ite_true] using found)
    exact sameResult ▸ certificate
  · exact stored.slots other result (by simpa only [store, put, same, ite_false] using found)

/-- The leaf bound includes both the captured target and the current immutable input. -/
def leafDepth (record : SourceEqualityClassOrder.Record) (path : EqualityNormalize.Path)
    (capturedDepth inputDepth : Nat) : Nat := max (targetDepth capturedDepth (operands record.paths path)) inputDepth

section Producers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next : Inventory}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : State width} {input value result : Value Symbol Guard} {memos final : Memos}

/-- The same actual force derives a universal miss certificate or reads its exact warm slot. -/
theorem force_receipt {receiptBase : InternedConstructorTemplates.State Symbol Guard}
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record values receiptBase path
      before value after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (stored : Stored record values before) (depth : Nat) (bounded : ∀ original ∈ values, Cap Plain depth original)
    (domains : ∀ operand ∈ operands record.paths path, Domain operand values) :
    Stored record values after ∧ Cap Plain (targetDepth depth (operands record.paths path)) value := by
  cases receipt.reads with
  | hit present => exact ⟨stored, stored.slots path value present depth bounded domains⟩
  | miss absent reads =>
      have available : Values before.checked.native.machine.heap values :=
        fun value member => ready.captured.available value (known value member)
      have produced := SourceCurrentConstrainedCapMixedTarget.target_reads depth reads ready.checked available
        ready.stored stored.merge stored.current bounded domains
      have certificate : Certificate record values path value := by
        intro otherDepth otherBounds otherDomains
        exact (SourceCurrentConstrainedCapMixedTarget.target_reads otherDepth reads ready.checked available
          ready.stored stored.merge stored.current otherBounds otherDomains).2.2
      exact ⟨store_stored record values before path value _ _ stored produced.2.1 produced.1 certificate, produced.2.2⟩

/-- The same actual leaf returns its explicit maximum depth without an all-path mask premise. -/
theorem leaf_receipt
    (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values base path input
      before result after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (stored : Stored record values before) (capturedDepth : Nat)
    (bounded : ∀ original ∈ values, Cap Plain capturedDepth original)
    (domains : ∀ operand ∈ operands record.paths path, Domain operand values)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (inputDepth : Nat) (inputCap : Cap Plain inputDepth input) :
    Stored record values after ∧ Cap Plain (leafDepth record path capturedDepth inputDepth) result := by
  cases receipt.reads with
  | apply first query =>
      have forced := force_receipt first ready known stored capturedDepth bounded domains
      have produced := SourceCurrentConstrainedCapCurrentNative.step _ formulas solver query.actual
        first.ready.checked.good first.ready.checked.semantic forced.1.current
        first.available (first.effects.keeps.available input available) first.closed closed
        (forced.2.mono (Nat.le_max_left _ _)) (inputCap.mono (Nat.le_max_right _ _))
      exact ⟨advance_stored record values _ _ forced.1 produced.1, produced.2.1⟩

end Producers
end MicroCFTA.SourceCurrentConstrainedCapMixedShared
