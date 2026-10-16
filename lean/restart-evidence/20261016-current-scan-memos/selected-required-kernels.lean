import MicroCFTA.SourceCurrentConjunctionSelectedRecords
import MicroCFTA.SourceCurrentConjunctionRequired
open MicroCFTA MicroCFTA.Language MicroCFTA.EqualityNormalize
open MicroCFTA.InternedConstructorTemplates MicroCFTA.InternedProbeProvenance
open MicroCFTA.InternedNestedProvenance (Values)
open MicroCFTA.SourceEqualityClassOrder
open MicroCFTA.SourceCurrentAllocatedNativeInventoryState (Inventory At)
open MicroCFTA.SourceCurrentConjunctionClassScan
open MicroCFTA.SourceCurrentConjunctionClassScanCompletion (Ranges)
open MicroCFTA.SourceCurrentConjunctionSelectedRecords
open MicroCFTA.SourceCurrentConjunctionRequired
open MicroCFTA.InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

-- The positional selected branch keeps its literal head, even when path fields can repeat.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {u reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {paths : Class} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {heap : State Symbol Guard} {memo saved : Memo}
    {primary : EndpointStatefulGateTrace.ClassTrace u reaches values paths before.native.machine.heap false heap}
    {rest : Scan budget u reaches values classes (advanceHeap before heap) memo outcome selected after saved}
    {record : Record} {records kept : List Record}
    (receipt : Retained (.selected primary rest) (record :: records) kept) :
    ∃ tail, kept = record :: tail := by
  have noTrue : ∀ target, ¬EndpointStatefulGateTrace.ClassTrace u reaches values paths
      before.native.machine.heap true target := by
    intro target other
    have impossible := EndpointStatefulGateTrace.class_trace_unique u reaches values paths
      before.native.machine.heap false true heap target primary other
    cases impossible.1
  cases receipt
  · exact ⟨_, rfl⟩
  all_goals exact False.elim (noTrue _ (by assumption))

-- Every retained occurrence is an original input record and has an actually selected path field.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {u reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before after : Checked width} {memo saved : Memo}
    {trace : Scan budget u reaches values classes before memo outcome selected after saved}
    {records kept : List Record} (receipt : Retained trace records kept) (record : Record) (member : record ∈ kept) :
    record ∈ records ∧ record.paths ∈ selected := by
  exact ⟨receipt.fields.1.subset member, receipt.fields.2 ▸ List.mem_map.mpr ⟨record, member, rfl⟩⟩

section Required
variable [DecidableEq (EdgeKey Symbol Guard)]
  {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
  {inventory : Inventory} {selected : Constraints} {values results : List (Value Symbol Guard)}
  {before after : Checked width}
  (receipt : Receipt formulas solver inventory selected values results before after)

-- Required reconstruction keeps both complete native memo states and the exact equality operations.
example : after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
    after.native.machine.domains = before.native.machine.domains ∧ after.operations = before.operations :=
  ⟨receipt.nodes, receipt.edges, receipt.domains, receipt.operations⟩

-- Stable completion supplies actual literal worker bounds at the same returned heap.
example : ∃ fuel readFuel, SourceEqualityRequiredExecution.requireAll fuel readFuel
    (SourceEqualitySelectedRequired.paths selected) values before.native.machine.heap = .done results after.native.machine.heap := by
  obtain ⟨fuel, readFuel, enough⟩ := receipt.stable
  exact ⟨fuel, readFuel, enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩

-- Result acceptance entails original acceptance and the exact required-path condition.
example (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (terms : List (Term Symbol)) (accepted : All₂ (meaning holds ambient) results terms) :
    All₂ (meaning holds ambient) values terms ∧
      SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms :=
  (receipt.language holds ambient terms).mp accepted

-- The original positional record determines each final selected-path domain.
example (kept : List Record) (same : kept.map Record.paths = selected)
    (record : Record) (member : record ∈ kept) (path : Path) (present : path ∈ record.paths) :
    SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results := by
  apply receipt.paths path
  apply List.mem_flatten.mpr
  exact ⟨record.paths, same ▸ List.mem_map.mpr ⟨record, member, rfl⟩, present⟩
end Required

-- Initial current invariants derive the required worker; no completed required callback is supplied.
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {budget : Nat} {u reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget u reaches values classes before memo none selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget u reaches values classes before memo) :
    ∃ results heap fuel readFuel, SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths selected) values after.native.machine.heap = .done results heap ∧
      (advanceHeap after heap).operations = after.operations := by
  obtain ⟨_, results, heap, receipt, _, _, _⟩ := scan_required_complete formulas solver inventory actual
    ready admitted available proper active correct ranges
  obtain ⟨fuel, readFuel, enough⟩ := receipt.stable
  exact ⟨results, heap, fuel, readFuel, enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _), receipt.operations⟩
