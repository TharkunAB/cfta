import MicroCFTA.SourceCurrentAllocatedSharedTargetForce

/-!
# Checked narrowing after shared target forcing

A leaf forces its class target, then intersects that returned target with
the current leaf input. Only that input must be closed.
The checked query retains the actual target slots and completed merge table.
The input inventory can change to the computed generated-query inventory.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedGuardedLanguage (meaning)
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State advance)
open SourceCurrentAllocatedSharedTargetForce (Force ForceRanges Retains)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Step" => SourceCurrentAllocatedTargetQuery.Step
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "requestNode" => SourceRecursiveIntersectionCode.requestNode
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable {width : Nat}

/-- Target forcing precedes the actual checked intersection at its returned state. -/
inductive Leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : Record) (values : List (Value Symbol Guard)) (path : Path) (input : Value Symbol Guard) :
    State width → Value Symbol Guard → State width → Prop where
  | apply (forced : Force record values path before target middle)
      (step : Step target input middle.checked result checked) :
      Leaf record values path input before result (advance middle checked)

/-- A range plan inspects only the actual returned target force. -/
def Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : Record) (values : List (Value Symbol Guard)) (path : Path)
    (input : Value Symbol Guard) (before : State width) : Prop :=
  ForceRanges record values path before ∧
    ∀ target middle, Force record values path before target middle →
      WordRanges (.code (requestNode emptyDomain target input)) middle.checked

/-- Global reads follow the actual target force and the same returned checked query. -/
inductive Reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {record : Record} → {values : List (Value Symbol Guard)} → {path : Path} → {input result : Value Symbol Guard} →
    {before after : State width} → Leaf record values path input before result after → Memos → Memos → Prop where
  | apply {forced : Force record values path before target middle}
      {step : Step target input middle.checked result checked}
      (first : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver forceInventory record values base path
        before target middle memos current)
      (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result checked current) :
      Reads formulas solver (.apply forced step) memos current

/-- Actual leaf narrowing retains every live cache and the captured class state. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (path : Path) (input : Value Symbol Guard)
    (before : State width) (result : Value Symbol Guard) (after : State width) (memos final : Memos) : Prop where
  actual : Leaf record values path input before result after
  reads : Reads formulas solver actual memos final
  ready : Ready formulas solver inventory record values base after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked)
  extension : SourceRecursiveIntersectionKernel.Extension before.checked.native.machine after.checked.native.machine
  available : Available after.checked.native.machine.heap result
  closed : result.free = []
  slots : Retains before after
  retained : Extends before.memo after.memo
  globals : SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap after.checked.native.machine.heap memos final
  narrows : ∀ ambient term, meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
    meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input term
  preserves : ∀ ambient symbol terms part,
    All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
    EqualityNormalize.ClassSat (.node symbol terms) record.paths →
    (Term.node symbol terms).atPath path = some part →
    meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input part →
    meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part

private theorem of_parts [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : Path} {input target result : Value Symbol Guard}
    {before middle : State width} {checked : Checked width} {memos current : Memos}
    (first : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver inventory record values base path
      before target middle memos current)
    (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result checked current) :
    Receipt formulas solver next record values base path input before result (advance middle checked) memos current := by
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

/-- Initial class support constructs target forcing and its actual checked leaf query. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : State width)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (input : Value Symbol Guard)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (ranges : Ranges record values path input before) (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ result after next final, Receipt formulas solver next record values base path input before result after memos final := by
  obtain ⟨target, middle, targetInventory, current, _, forced⟩ := SourceCurrentAllocatedSharedTargetForce.complete
    formulas solver inventory record values base before ready known domains coherent active path member ranges.1 memos valid
  obtain ⟨next, result, checked, _, _, query⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver targetInventory target input middle.checked forced.ready.checked forced.ready.admitted
    forced.available (forced.effects.keeps.available input available) forced.closed closed
    (ranges.2 target middle forced.actual) current forced.globals.valid
  exact ⟨result, advance middle checked, next, current, of_parts forced query⟩

/-- Every actual completed leaf derives its result law from the same force and query. -/
theorem Leaf.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {record : Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : Path} {input result : Value Symbol Guard}
    {before after : State width} (actual : Leaf record values path input before result after)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (ranges : Ranges record values path input before) (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ next final, Receipt formulas solver next record values base path input before result after memos final := by
  cases actual with
  | apply forced step =>
      obtain ⟨targetInventory, current, forceReceipt⟩ := SourceCurrentAllocatedSharedTargetForce.Force.verified
        formulas solver inventory forced ready known domains coherent active member ranges.1 memos valid
      obtain ⟨next, _, _, query⟩ := SourceCurrentAllocatedTargetQuery.Step.verified
        formulas solver targetInventory step forceReceipt.ready.checked forceReceipt.ready.admitted
        forceReceipt.available (forceReceipt.effects.keeps.available input available) forceReceipt.closed closed
        (ranges.2 _ _ forced) current forceReceipt.globals.valid
      exact ⟨next, current, of_parts forceReceipt query⟩

/-- Leaf heap growth retains the same previously correct fourth emptiness table. -/
theorem Receipt.fourth_correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : Path} {input result : Value Symbol Guard}
    {before after : State width} {memos final : Memos}
    (receipt : Receipt formulas solver inventory record values base path input before result after memos final)
    (memo : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.checked.native.machine.heap memo) :
    SourceCurrentEmptinessMemo.Correct formulas solver after.checked.native.machine.heap memo :=
  SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps memo correct

end MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf
