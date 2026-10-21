import MicroCFTA.SourceCurrentAllocatedClassTarget

/-!
# Shared target slots in the full allocated checked state

Each slot retains its exact earlier target graph and its completed reads.
The historical inventory is independent of the current inventory. Heap
and merge-table growth retain the same captured forest and target law.
Initial state construction clears only class-local target slots.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedTargetState
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceEqualityClassTarget (operandPaths)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "ClassReady" => SourceCurrentConjunctionClassScan.Ready
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable {width : Nat}

/-- Class-local slots share the complete current checked state and warm merge memo. -/
structure State (width : Nat) where
  checked : Checked width
  targets : EqualityNormalize.Path → Option (Value Symbol Guard)
  memo : Memo

/-- Start a class with empty slots and the supplied checked state and merge table. -/
def initial (checked : Checked width) (memo : Memo) : State width := ⟨checked, fun _ => none, memo⟩

/-- Advance checked execution without replacing slots or the merge table. -/
def advance (state : State width) (checked : Checked width) : State width := {state with checked := checked}

/-- A completed first force stores its literal result and both returned states. -/
def store (state : State width) (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (checked : Checked width) (memo : Memo) : State width := ⟨checked, put state.targets path value, memo⟩

/-- A returned slot retains its exact historical target, reads, and independent language receipt. -/
def SlotReceipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (heap : Heap) (memo : Memo) (path : EqualityNormalize.Path) (value : Value Symbol Guard) : Prop :=
  path ∈ record.paths ∧ ∃ (before after : Checked width) (next : Inventory) (initial saved : Memo) (memos final : Memos),
    ∃ actual : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path) before initial value after saved,
      SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final ∧
      SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values (operandPaths record.paths path)
        before initial value after saved memos final ∧ Keeps after.native.machine.heap heap ∧ Extends saved memo

/-- Current readiness retains every historical slot without identifying its inventory with the current one. -/
structure Ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : Heap) (state : State width) : Prop where
  checked : ClassReady state.checked
  admitted : At formulas solver inventory state.checked
  captured : Keeps base state.checked.native.machine.heap
  stored : Stored state.checked.native.machine.heap state.memo
  covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient state.memo
  receipts : ∀ path value, state.targets path = some value →
    SlotReceipt width formulas solver record values state.checked.native.machine.heap state.memo path value

/-- Empty slots need no historical target assumptions. -/
theorem initial_ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (base : Heap)
    (checked : Checked width) (memo : Memo) (ready : ClassReady checked)
    (admitted : At formulas solver inventory checked) (captured : Keeps base checked.native.machine.heap)
    (stored : Stored checked.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo) :
    Ready formulas solver inventory record values base (initial checked memo) :=
  ⟨ready, admitted, captured, stored, covered, by intro path value absent; cases absent⟩

/-- Growth retains the same historical graph, inventory, and complete merge result. -/
theorem SlotReceipt.grows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {before after : Heap}
    {memo saved : Memo} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : SlotReceipt width formulas solver record values before memo path value)
    (keeps : Keeps before after) (retained : Extends memo saved) :
    SlotReceipt width formulas solver record values after saved path value := by
  obtain ⟨member, first, last, next, initial, completed, memos, final, actual, reads, result, growth, entries⟩ := receipt
  exact ⟨member, first, last, next, initial, completed, memos, final, actual, reads, result,
    growth.trans keeps, extends_trans entries retained⟩

/-- The historical receipt derives current availability and closedness without a new domain premise. -/
theorem SlotReceipt.available [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {heap : Heap}
    {memo : Memo} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : SlotReceipt width formulas solver record values heap memo path value) :
    Available heap value ∧ value.free = [] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, result, growth, _⟩ := receipt
  exact ⟨growth.available value result.available, result.closed⟩

/-- Independent selected-term meaning survives every later inventory change. -/
theorem SlotReceipt.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {heap : Heap}
    {memo : Memo} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    (receipt : SlotReceipt width formulas solver record values heap memo path value)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths) :
    SourceCurrentAllocatedClassTarget.SelectedIncludes formulas solver record values path value := by
  obtain ⟨member, _, _, _, _, _, _, _, _, _, result, _, _⟩ := receipt
  exact SourceCurrentAllocatedClassTarget.receipt_included result coherent active member

/-- Actual checked effects retain slots while their current admission inventory can change. -/
theorem Ready.advance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap}
    {before : State width} (ready : Ready formulas solver inventory record values base before)
    (next : Inventory) (checked : Checked width) (nextReady : ClassReady checked)
    (nextAt : At formulas solver next checked)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical checked)) :
    Ready formulas solver next record values base (SourceCurrentAllocatedSharedTargetState.advance before checked) :=
  ⟨nextReady, nextAt, ready.captured.trans effects.keeps, ready.stored.grows effects.keeps, ready.covered,
    fun path value present => (ready.receipts path value present).grows effects.keeps (extends_refl _)⟩

/-- Constructor effects derive checked readiness and admission with all slots unchanged. -/
theorem Ready.physical [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap}
    {before : State width} (ready : Ready formulas solver inventory record values base before)
    (after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) after) :
    Ready formulas solver inventory record values base
      (SourceCurrentAllocatedSharedTargetState.advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked after)) := by
  apply ready.advance inventory _ (SourceCurrentConjunctionClassScan.advance_ready before.checked after ready.checked effects)
  · exact ready.admitted.advance after (SourceCurrentAllocatedQueryMemo.advance_extension before.checked after effects)
  · exact effects

/-- The actual completed target stores its new inventory and retains every earlier slot history. -/
theorem Ready.store [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap}
    {before : State width} (ready : Ready formulas solver inventory record values base before)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    {value : Value Symbol Guard} {after : Checked width} {saved : Memo} {memos final : Memos}
    (actual : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path) before.checked before.memo value after saved)
    (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final)
    (receipt : SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values (operandPaths record.paths path)
      before.checked before.memo value after saved memos final) :
    Ready formulas solver next record values base (SourceCurrentAllocatedSharedTargetState.store before path value after saved) := by
  refine ⟨receipt.ready, receipt.admitted, ready.captured.trans receipt.effects.keeps,
    receipt.stored, receipt.covered, ?_⟩
  intro other target present
  by_cases same : other = path
  · subst other
    have equal : value = target := by simpa only [SourceCurrentAllocatedSharedTargetState.store, put, ite_true, Option.some.injEq] using present
    subst target
    exact ⟨member, before.checked, after, next, before.memo, saved, memos, final, actual, reads, receipt,
      pure_keeps _ receipt.ready.semantic.ready, extends_refl _⟩
  · have original : before.targets other = some target := by simpa only [SourceCurrentAllocatedSharedTargetState.store, put, same, ite_false] using present
    exact (ready.receipts other target original).grows receipt.effects.keeps receipt.retained

end MicroCFTA.SourceCurrentAllocatedSharedTargetState
