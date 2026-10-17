import MicroCFTA.SourceCurrentConstrainedCapSharedSupport
import MicroCFTA.SourceCurrentConstrainedCapEditSupport
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorker

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.PathEditSharedChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityAnnotationLanguage SourceCurrentConstrainedCapPaths
open SourceCurrentConstrainedCapSharedSupport
open SourceCurrentConstrainedCapEditSupport (AtLeaves)
open SourceCurrentAllocatedSharedTargetState (State advance)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "Preserves" => SourceCurrentConstrainedCapRequiredSupport.Preserves

private theorem join_receipts [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : Heap} {path : EqualityNormalize.Path} {input target result : Value Symbol Guard}
    {before middle : State width} {checked : SourceEqualityNativeDemand.State width} {memos current : Memos}
    (first : ForceReceipt formulas solver inventory record values base path before target middle memos current)
    (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result checked current) :
    LeafReceipt formulas solver next record values base path input before result (advance middle checked) memos current := by
  have queryGlobal : SourceCurrentSubsumesQueryMemos.Effect middle.checked.native.machine.heap checked.native.machine.heap current current :=
    ⟨query.effects.keeps, query.ready.semantic, query.ready.costs, query.globals, extends_refl _, rfl⟩
  refine ⟨.apply first.actual query.actual,
    .apply (forced := first.actual) (step := query.actual) first query,
    first.ready.advance next checked query.ready query.admitted query.effects,
    first.effects.trans query.effects, first.extension.trans query.extension,
    query.available, query.closed, first.slots, first.retained,
    SourceCurrentMemoMergeQueryMemos.effect_trans first.globals queryGlobal, ?_, ?_⟩
  · intro ambient term accepted
    exact ((query.meaning ambient term).mp accepted).2
  · intro ambient symbol terms part accepted satisfied selected present
    exact (query.meaning ambient part).mpr ⟨first.included ambient symbol terms part accepted satisfied selected, present⟩

/-- A supplied actual first miss produces a causal slot, then a constructed zero-bound warm force feeds the actual leaf query. -/
theorem miss_warm_leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory firstInventory next : Inventory) (record : SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (base : Heap) (path : EqualityNormalize.Path)
    (before middle : State width) (target input result : Value Symbol Guard)
    (checked : SourceEqualityNativeDemand.State width) (memos current : Memos)
    (first : ForceReceipt formulas solver firstInventory record values base path before target middle memos current)
    (absent : before.targets path = none)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (closed : ClosedValues values) (stored : Stored record values before)
    (supported : ∀ operand ∈ SourceEqualityClassTarget.operandPaths record.paths path, ForestSupported Plain operand values)
    (available : Available before.checked.native.machine.heap input) (inputClosed : input.free = []) (annotated : Annotated Plain input)
    (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result checked current) :
    before.targets path ≠ middle.targets path ∧
    SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record values path middle = .done target middle ∧
    ∃ actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record values path input middle result (advance middle checked),
      SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual current current ∧
      Stored record values (advance middle checked) ∧ Annotated Plain result ∧ Preserves Plain input result := by
  have firstLocal := force_receipt first ready known closed stored supported
  have changed : before.targets path ≠ middle.targets path := by rw [absent, first.present]; exact nofun
  have warm : SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record values path middle = .done target middle :=
    SourceCurrentAllocatedSharedTargetWorker.force_hit 0 0 0 0 0 record values path middle target first.present
  have physicalReady : SourceCurrentConjunctionRowsAllocation.Ready (SourceCurrentAllocatedNativeEffects.physical middle.checked) :=
    ⟨first.ready.checked.semantic, first.ready.checked.costs, first.ready.checked.good.operations, first.ready.checked.good.fields⟩
  have effects := SourceCurrentConjunctionRowsAllocation.Effects.refl _ physicalReady
  have forced : ForceReceipt formulas solver firstInventory record values base path middle target middle current current :=
    ⟨.hit first.present, .hit first.present current, first.ready, effects, .refl _,
      first.available, first.closed, first.present, .refl _, extends_refl _,
      ⟨effects.keeps, first.ready.checked.semantic, first.ready.checked.costs, first.globals.valid, extends_refl _, rfl⟩,
      first.included⟩
  have leaf := join_receipts forced query
  have localResult := leaf_receipt leaf first.ready known closed firstLocal.1 supported
    (first.effects.keeps.available input available) inputClosed annotated
  exact ⟨changed, warm, leaf.actual, leaf.reads, localResult.1, localResult.2,
    SourceCurrentConstrainedCapEditSupport.preserves_of_annotated Plain input result localResult.2⟩

/-- Actual leaf production retains outstanding masks on both sides of a prefix overlap. -/
theorem prefix_overlaps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : Heap} {token : EqualityNormalize.Path} {before after : State width} {input result : Value Symbol Guard} {memos final : Memos}
    (receipt : LeafReceipt formulas solver next record values base token input before result after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (closed : ClosedValues values) (stored : Stored record values before)
    (supported : ∀ operand ∈ SourceEqualityClassTarget.operandPaths record.paths token, ForestSupported Plain operand values)
    (available : Available before.checked.native.machine.heap input) (inputClosed : input.free = []) (annotated : Annotated Plain input)
    (stem suffix : List Int) (ancestor : Supported Plain stem input) (descendant : Supported Plain (stem ++ suffix) input)
    (edits : SourceEqualityEdits.Edits EqualityNormalize.Path) (placed : AtLeaves Plain edits input) :
    Stored record values after ∧ Supported Plain stem result ∧ Supported Plain (stem ++ suffix) result ∧ AtLeaves Plain edits result := by
  have produced := leaf_receipt receipt ready known closed stored supported available inputClosed annotated
  have retained := SourceCurrentConstrainedCapEditSupport.preserves_of_annotated Plain input result produced.2
  exact ⟨produced.1, retained stem ancestor, retained (stem ++ suffix) descendant,
    SourceCurrentConstrainedCapEditSupport.placement_preserved retained placed⟩

end MicroCFTA.PathEditSharedChecks

#print axioms MicroCFTA.PathEditSharedChecks.miss_warm_leaf
#check @MicroCFTA.PathEditSharedChecks.miss_warm_leaf
#print axioms MicroCFTA.PathEditSharedChecks.prefix_overlaps
#check @MicroCFTA.PathEditSharedChecks.prefix_overlaps
